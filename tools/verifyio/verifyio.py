import argparse, time, sys, os, re, json
from recorder_reader import RecorderReader
from read_nodes import read_verifyio_nodes_and_conflicts
from match_mpi import match_mpi_calls
from verifyio_graph import VerifyIONode, VerifyIOGraph

"""
A data structure to make it easier
to pass around infomration
"""
class VerifyIO:
    def __init__(self, args):
        self.semantics = args.semantics             # Semantics to check
        self.algorithm = args.algorithm             # Algorithm for verification
        self.show_summary = args.show_summary       # whether to show summary in the end
        self.show_details = args.show_details       # whether to show violation details
        self.show_full_chain = args.show_full_chain # whether to show full call chain
        self.show_callsite = args.show_callsite     # whether to show source locations of violations
        self.json_path = args.json                  # write violations grouped by call site to this file
        self.traces_folder = args.traces_folder
        self.violation_groups = {}                  # used by --json
        # per-violation details are only collected when some output needs them
        self.collect_violations = (self.show_summary or self.show_details or
                                   self.show_callsite or bool(self.json_path))
        if self.semantics == "Custom":
            self.semantic_string = args.semantic_string # Custom semantics string
        self.reader = None                          # RecorderReader
        self.G = None                               # Happens-before Graph (VerifyIOGraph)
        self.all_nodes = None                       # Per-rank VerifyIONode list

    def next_po_node(self, n, funcs):
        if self.G:
            return vio.G.next_po_node(n, funcs)
        else:
            if not funcs:
                return self.all_nodes[n.rank][n.index+1]
            for i in range(n.index+1, len(self.all_nodes[n.rank]), 1):
                if self.all_nodes[n.rank][i].func in funcs:
                    return self.all_nodes[n.rank][i]

    def prev_po_node(self, n, funcs):
        if self.G:
            return self.G.prev_po_node(n, funcs)
        else:
            if not funcs:
                return self.all_nodes[n.rank][n.index-1]
            for i in range(n.index-1, 0, -1):
                if self.all_nodes[n.rank][i].func in funcs:
                    return self.all_nodes[n.rank][i]

    def next_hb_node(self, n, funcs):
        if self.G:
            return self.G.next_hb_node(n, funcs)
        # TODO: get next hb node withouth graph.


"""
Verify for a given conflicting pair of (c1, c2),
whether c1 happens-before c2 for the given consistency
semantics.

For POSIX semantics:
    - check c1 hb-> c2
For Commit semantics:
    - check c1 hb-> commit hb-> c2
For Session semantics:
    - check if c1 po-> close-hb-open po-> c2
For MPI-IO semantics:
    - check if c1 po-> sync-hb-sync po-> c2

We have four alogorithms:
Algo 1. Graph Reachibility (e.g., DFS)
Algo 2. Transitivive Closure
Algo 3. Vector Clock
Algo 4. On-the-fly MPI Check

TODO: choose algorithm dynamically
"""
def verify_pair_proper_synchronization(n1, n2, vio):

    # First check if the I/O operations are protected
    # by locks (e.g., flock() or fcntl())
    # TODO: this is just a wordaround, as we only check
    # for the existence of those calls. We did not check
    # for lock acquire/realse or whther the file name is
    # the same as the I/O. This workaround works for the
    # tests we have.
    for r in vio.reader.records[n1.rank][n1.seq_id-5:n1.seq_id+5]:
        func_name = vio.reader.funcs[r.func_id]
        if func_name == "fcntl" or func_name == "flock":
            return True

    v1, v2 = None, None

    if vio.semantics == "POSIX":
        v1 = n1
        v2 = n2
    elif vio.semantics == "Commit":
        v1 = vio.next_po_node(n1, ["fsync", "close", "fclose"])
        v2 = n2
    elif vio.semantics == "Session":
        v1 = vio.next_po_node(n1, ["close", "fclose", "fsync"])
        v2 = vio.prev_po_node(n2, ["open",  "fopen",  "fsync"])
    elif vio.semantics == "MPI-IO":
        next_sync = vio.next_po_node(n1, ["MPI_File_close", "MPI_File_sync"])
        prev_sync = vio.prev_po_node(n2, ["MPI_File_open",  "MPI_File_sync"])
        if (not next_sync) or (not prev_sync): return False
        if vio.algorithm == 4:
            v1 = next_sync
        else:
            # now we have two syncs
            # check for the "barrier" of sync-barr-sync
            # pass in funcs=None to get the immediate next/prev po node.
            v1 = vio.next_po_node(next_sync, None)
        v2 = prev_sync
    elif vio.semantics == "Custom":
        v1, v2 = custom_semantic(vio.semantic_string, n1, n2)

    if (not v1) or (not v2):
        return False

    # Algorithm 1: Graph Reachibility
    if vio.algorithm == 1:
        return vio.G.has_path(v1, v2)

    # Algorithm 2: Transitivive
    if vio.algorithm == 2:
        print("transitive closure is alwasy slower than vector clock")
        print("use vector clock instead")
        vio.algorithm = 3
        pass

    # Algorithm 3: Vector Clock
    if vio.algorithm == 3:
        vc1 = vio.G.get_vector_clock(v1)
        vc2 = vio.G.get_vector_clock(v2)
        return (bool)(vc1[v1.rank] < vc2[v1.rank])

    # Algorithm 4: On-the-fly MPI check
    if vio.algorithm == 4:
        # O(N) where N is remaining calls after v1
        for next_mpi_call in vio.all_nodes[v1.rank][v1.index+1:]:
            mpi_edge = mapped_mpi_edges[v1.rank].get(next_mpi_call.seq_id)
            if mpi_edge and mpi_edge[v2.rank]:
                if mpi_edge[v2.rank].seq_id < v2.seq_id:
                    return True
                else:
                    return False
        return False


"""
For an execution, iterate through every conflicting pairs
and verify if each conflict pair is properly synchornized for
the given consistency semantics

 - conflict_pairs: list of (n1, n2s)
    n1:  seq_id of conflicting I/O operation
    n2s: list of seq id of I/O operations conflicting with n1.
"""
def verify_execution_proper_synchronization(conflict_pairs, vio:VerifyIO):

    total_conflicts = 0
    total_violations = 0

    summary = {
        'c_ranks_cnt': [[0 for _ in range(vio.reader.nprocs)] for _ in range(vio.reader.nprocs)],
        'c_files_cnt': {},
        'c_functions_cnt': {}
    }

    for pair in conflict_pairs:

        # n1: conflict I/O operation (VerifyIONode)
        # n2s: conflicting I/O operations (array of VerifyIONode)
        n1, n2s = pair[0], pair[1]

        s = 0
        for i in range(len(n2s)):
            s += len(n2s[i])
        debug_str = f"Verify: {n1} {s} pairs"
        t1 = time.time()

        for rank in range(len(n2s)):
            if len(n2s[rank]) < 1: continue
            total_conflicts += len(n2s[rank])

            # check if n1 happens-before the first node of n2s[rank]
            # if n1 hb-> n2s[rank][0], then n1 hb-> n2s[rank][:]
            if verify_pair_proper_synchronization(n1, n2s[rank][0], vio):
                debug_str += f", n1 -> n2s[{rank}][0]"
                continue

            # check if the last node of n2s[rank] happens-beofre n1
            # if n2s[rank][-1] hb->hb, then n2s[rank][:] hb-> n1
            if verify_pair_proper_synchronization(n2s[rank][-1], n1, vio):
                debug_str += f", n2s[{rank}][-1] -> n1"
                continue

            # check if n1 happens-before the last node of n2s[rank]
            # if not, then n1 is certainly not ->hb any nodes of n2s[rank]
            # similarly, if n2s[rank][0] does not happen-before n1, then
            # non of n2s[rank] will happen-before n1.
            if (not verify_pair_proper_synchronization(n1, n2s[rank][-1], vio)) \
                and (not verify_pair_proper_synchronization(n2s[rank][0], n1, vio)):
                total_violations += len(n2s[rank])
                for n2 in n2s[rank]:
                    if vio.collect_violations:
                        get_violation_info([n1, n2], vio, summary, False)
                    #print(f"{vio.semantics} violation: {n1} {n2}")
                continue

            # now we are here, its very likely that n1 is not
            # properly-synchornized with any node of n2s[rank],
            # but we still need to go through evey pair to make sure.
            # TODO we could do the previous three checks recursively.
            for n2 in n2s[rank]:
                this_pair_ok = (verify_pair_proper_synchronization(n1, n2, vio) or \
                                verify_pair_proper_synchronization(n2, n1, vio))
                if not this_pair_ok:
                    if vio.collect_violations:
                        get_violation_info([n1, n2], vio, summary, this_pair_ok)
                    total_violations += 1
                    #print(f"{vio.semantics} violation: {n1} {n2}")

        t2 = time.time()
        #print(debug_str+", time: %.3f" %(t2-t1))

    if vio.show_summary:
        print_summary(summary)
    print("Total semantic violations: %d" %total_violations)
    print("Total conflict pairs: %d" %total_conflicts)
    if vio.json_path:
        write_json_report(vio, total_violations, total_conflicts)


# A helper function to map the mpi edges to a 3D data structure 
# to reduce the search time without changing the original mpi_edges
def map_edges(mpi_edges, reader):
    num_ranks = reader.nprocs
    edges = [{} for _ in range(num_ranks)]

    for e in mpi_edges:
        calls = e.get_all_involved_calls()
        for c in calls:
            edges[c.rank][c.seq_id] = [None] * num_ranks
            for t in calls:
                edges[c.rank][c.seq_id][t.rank] = t
    return edges


def get_shortest_path(G:VerifyIOGraph, src:VerifyIONode, dst:VerifyIONode):
    path = G.shortest_path(src, dst)
    path_str = ""
    for i in range(len(path)):
        node = path[i]
        path_str += str(node) 
        if i != len(path) - 1:
            path_str += "->"
    return path_str


def print_summary(summary):
    print("=" * 80)
    print("Details".center(80))
    print("=" * 80)

    print(f"{'Rank':<10} {'Conflicts':<20}")
    print("-" * 30)
    for index, value in enumerate([sum(values) for values in zip(*summary['c_ranks_cnt'])]):
        print(f"{index:<10} {value:<20}")
    print()

    print(f"{'File':<50} {'Conflicts':<20}")
    print("-" * 70)
    for key, count in summary['c_files_cnt'].items():
        print(f"{key:<50} {count:<20}")
    print()

    print(f"{'Function Call':<50} {'Conflicts':<20}")
    print("-" * 70)
    for key, count in summary['c_functions_cnt'].items():
        print(f"{key:<50} {count:<20}")
    print("=" * 80)
    

def get_location(rank, record, reader):
    """Source location of a record's call site with normalized paths, or None.
    "a/b/../../c/file.c:12 in f <- ..." -> "c/file.c:12 in f <- ..." """
    loc = reader.get_callsite(rank, record.call_site)
    if loc is None:
        return None
    frames = []
    for frame in loc.split(" <- "):
        path, sep, rest = frame.partition(":")
        frames.append(os.path.normpath(path) + sep + rest)
    return " <- ".join(frames)


def get_call_stack(node, reader):
    """Records of the call stack of node, innermost (the I/O call) first:
    for every call depth, the closest preceding record at that depth."""
    stack = []
    seq_id = node.seq_id
    depth = reader.records[node.rank][seq_id].call_depth
    while True:
        r = reader.records[node.rank][seq_id]
        if r.call_depth <= depth:
            stack.append(r)
            depth = r.call_depth - 1
        if r.call_depth == 0 or seq_id == 0:
            break
        seq_id -= 1
    return stack


def access_kind(func):
    return "write" if "write" in func else "read" if "read" in func else func


def site_info(node, reader):
    """Outermost call (the one the application made) plus the whole chain, for --json."""
    stack = get_call_stack(node, reader)
    root = stack[-1]
    loc = get_location(node.rank, root, reader)
    info = {"call": reader.funcs[root.func_id], "location": loc,
            "file": None, "line": None, "function": None}
    m = re.match(r"^(.*?):(\d+)(?: in (\S+))?", loc or "")
    if m:
        info["file"], info["line"], info["function"] = m.group(1), int(m.group(2)), m.group(3)
    info["chain"] = [{"call": reader.funcs[r.func_id], "location": get_location(node.rank, r, reader)}
                     for r in reversed(stack)]
    info["access"] = access_kind(node.func)
    return info


def add_violation_to_groups(nodes, file, vio):
    """Group violations by the pair of application call sites (order-independent)."""
    sites = [site_info(n, vio.reader) for n in nodes]
    keys = [(s["call"], s["location"], s["access"]) for s in sites]
    if keys[1] < keys[0]:
        keys.reverse(); sites.reverse(); nodes = nodes[::-1]
    key = tuple(keys)
    g = vio.violation_groups.get(key)
    if g is None:
        g = vio.violation_groups[key] = {
            "violations": 0,
            "kind": "%s-%s" % (sites[0]["access"], sites[1]["access"]),
            "files": {}, "rank_pairs": {},
            "site_a": sites[0], "site_b": sites[1],
            "example": {"rank_a": nodes[0].rank, "seq_a": nodes[0].seq_id,
                        "rank_b": nodes[1].rank, "seq_b": nodes[1].seq_id},
        }
    g["violations"] += 1
    g["files"][file] = g["files"].get(file, 0) + 1
    rp = "%d-%d" % (nodes[0].rank, nodes[1].rank)
    g["rank_pairs"][rp] = g["rank_pairs"].get(rp, 0) + 1


def write_json_report(vio, total_violations, total_conflicts):
    groups = sorted(vio.violation_groups.values(), key=lambda g: -g["violations"])
    for i, g in enumerate(groups):
        g["group_id"] = i + 1
    report = {
        "trace_dir": os.path.abspath(vio.traces_folder),
        "semantics": vio.semantics,
        "algorithm": vio.algorithm,
        "total_violations": total_violations,
        "total_conflict_pairs": total_conflicts,
        "callsites_available": any(g["site_a"]["location"] for g in groups),
        "groups": groups,
    }
    with open(vio.json_path, "w") as f:
        json.dump(report, f, indent=1)


def get_violation_info(nodes: list, vio, summary, this_pair_ok):

    def get_call_full_chain(node, reader):
        call_chain = []
        seq_id = node.seq_id
        while reader.records[node.rank][seq_id].call_depth > 0:
            call_chain.append(reader.records[node.rank][seq_id])
            seq_id -= 1
        call_chain.append(reader.records[node.rank][seq_id])
        return call_chain

    def get_call_partial_chain(node, reader):
        call_chain = []
        seq_id = node.seq_id
        added_depths = set()
        
        while reader.records[node.rank][seq_id].call_depth > 0:
            current_record = reader.records[node.rank][seq_id]
            if current_record.call_depth not in added_depths:
                call_chain.append(current_record)
                added_depths.add(current_record.call_depth)
            seq_id -= 1
        
        root_record = reader.records[node.rank][seq_id]
        if root_record.call_depth not in added_depths:
            call_chain.append(root_record)
        
        return call_chain

    def get_call_chain(node, reader, show_full_chain=False):
        if show_full_chain:
            return get_call_full_chain(node=node, reader=reader)
        else:
            return get_call_partial_chain(node=node, reader=reader)

    def update_function_count(func_id, summary, reader):
        func_name = reader.funcs[func_id]
        summary['c_functions_cnt'][func_name] = summary['c_functions_cnt'].get(func_name, 0) + 1

    def build_call_chain_str(call_chain, reader):
        return "-->".join(reader.funcs[cc.func_id] for cc in call_chain)

    def build_callsite_str(rank, record, reader):
        loc = get_location(rank, record, reader) or "unknown call site"
        return f"{reader.funcs[record.func_id]} ({loc})"

    left_call_chain = get_call_chain(nodes[0], vio.reader, vio.show_full_chain)
    right_call_chain = get_call_chain(nodes[1], vio.reader, vio.show_full_chain)
    file = vio.reader.records[nodes[0].rank][nodes[0].seq_id].args[0].decode('utf-8')
    if len(left_call_chain) > 0 and len(right_call_chain) > 0:
        summary['c_ranks_cnt'][nodes[0].rank][nodes[1].rank] += 1
        if file not in summary['c_files_cnt']:
            summary['c_files_cnt'][file] = 0
        summary['c_files_cnt'][file] += 1
        update_function_count(left_call_chain[-1].func_id, summary, vio.reader)
        update_function_count(right_call_chain[-1].func_id, summary, vio.reader)
        if vio.show_details:
            r_str = build_call_chain_str(right_call_chain, vio.reader)
            l_str = build_call_chain_str(reversed(left_call_chain), vio.reader)
            print(f"{nodes[0]}: {l_str} <--> {nodes[1]}: {r_str} on file {file}, properly synchronized: {this_pair_ok}")
        if vio.show_callsite:
            # the outermost call of each chain, i.e., the one the application made
            l_str = build_callsite_str(nodes[0].rank, left_call_chain[-1], vio.reader)
            r_str = build_callsite_str(nodes[1].rank, right_call_chain[-1], vio.reader)
            print(f"Rank {nodes[0].rank}: {l_str} <--> Rank {nodes[1].rank}: {r_str} on file {file}")
        if vio.json_path:
            add_violation_to_groups(nodes, file, vio)



def custom_semantic(str=None, n1:VerifyIO =None, n2: VerifyIO = None):

    def get_offset(s):
        s = s.split(":")[1].split("[")[0]
        return int(s[1:]) if "+" in s else int(s) if "-" in s else 0

    def get_node(conflict_str, node):
        offset = get_offset(conflict_str)
        if offset == 0:
            return node

        sync_arr = conflict_str.split("[")[1].split("]")[0].split(",")
        po_node_fn = vio.next_po_node if offset > 0 else vio.prev_po_node
        return po_node_fn(node, sync_arr if sync_arr else None)
    
    c1, c2 = str.split("&")
    return get_node(c1, n1), get_node(c2, n2)

    




if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("traces_folder")
    parser.add_argument("--semantics", type=str, choices=["POSIX", "MPI-IO", "Commit", "Session", "Custom"],
                        default="MPI-IO", help="Verify if I/O operations are properly synchronized under the specific semantics")
    parser.add_argument("--algorithm", type=int, choices=[1, 2, 3, 4],
                        default=3, help="1: graph reachibility, 2: transitive closure, 3: vector clock, 4: on-the-fly MPI check")
    parser.add_argument("--semantic_string", type=str, default="c1:+1[MPI_File_close, MPI_File_sync] & c2:-1[MPI_File_open, MPI_File_sync]")
    parser.add_argument("--show_details", action="store_true", help="Show details of the conflicts")
    parser.add_argument("--show_summary", action="store_true", help="Show summary of the conflicts")
    parser.add_argument("--show_full_chain", action="store_true", help="Show the full call chain of the conflicts")
    parser.add_argument("--show_callsite", action="store_true",
                        help="Show the outermost call of each conflict and its source location (needs a FULL_TRACING trace)")
    parser.add_argument("--json", type=str, metavar="FILE",
                        help="Write the violations, grouped by the pair of application call sites, as JSON to FILE")
    args = parser.parse_args()

    vio = VerifyIO(args)
    #import psutil
    #print('1. RAM Used (GB):', psutil.virtual_memory()[3]/1000000000)

    t1 = time.time()
    vio.reader = RecorderReader(args.traces_folder)
    #print('2. RAM Used (GB):', psutil.virtual_memory()[3]/1000000000)

    vio.all_nodes, conflicts = read_verifyio_nodes_and_conflicts(vio.reader)
    t2 = time.time()
    print("Step 1. read trace records and conflicts time: %.3f secs" %(t2-t1))
    #print('3. RAM Used (GB):', psutil.virtual_memory()[3]/1000000000)

    # TODO: do we need to sort here?
    # the recorder traces should be sorted already
    # and the conflict operations are also sorted before writing out.
    #
    # Set the index of each node with respect to per-rank VerifyIONode list
    # this index will be used later to accelerate next_po_node/prev_po_node
    for rank in range(vio.reader.nprocs):
        vio.all_nodes[rank] = sorted(vio.all_nodes[rank], key=lambda x: x.seq_id)
        for i, n in enumerate(vio.all_nodes[rank]): n.index = i
    #print('5. RAM Used (GB):', psutil.virtual_memory()[3]/1000000000)

    # get mpi calls and matched edges
    t1 = time.time()
    mpi_edges = match_mpi_calls(vio.reader)
    t2 = time.time()
    #print('6. RAM Used (GB):', psutil.virtual_memory()[3]/1000000000)
    print("Step 2. match mpi calls: %.3f secs, mpi edges: %d" %((t2-t1),len(mpi_edges)))

    if vio.algorithm !=4:
        t1 = time.time()
        vio.G = VerifyIOGraph(vio.all_nodes, mpi_edges, include_vc=True)
        t2 = time.time()
        print("Step 3. build happens-before graph: %.3f secs, nodes: %d" %((t2-t1), vio.G.num_nodes()))
        #print('7. RAM Used (GB):', psutil.virtual_memory()[3]/1000000000)

        # Correct code (traces) should generate a DAG without any cycles
        if vio.G.check_cycles(): quit()

        if vio.algorithm == 2 or vio.algorithm == 3:
            t1 = time.time()
            vio.G.run_vector_clock()
            #vio.G.run_transitive_closure()
            t2 = time.time()
            print("Step 4. run vector clock algorithm: %.3f secs" %(t2-t1))
            #print('8. RAM Used (GB):', psutil.virtual_memory()[3]/1000000000)
            # vio.G.plot_graph("vgraph.jpg")
    else:
        mapped_mpi_edges = map_edges(mpi_edges, vio.reader)

    t1 = time.time()
    verify_execution_proper_synchronization(conflicts, vio)
    t2 = time.time()
    print("Step 5. %s semantics verification time: %.3f secs" %(vio.semantics, t2-t1))
    #print('9. RAM Used (GB):', psutil.virtual_memory()[3]/1000000000)
