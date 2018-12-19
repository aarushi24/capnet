--------------------------- MODULE SecureProvider ---------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT NULL, Consumer, Provider, NewNode, cmem

(*--algorithm secureProvider
variables
    Nodes = {Consumer, Provider, NewNode},
    AllMem = {cmem},
    requestInstall = FALSE, 
    completeInstall = FALSE,
    useService = FALSE,
    rp = [n \in Nodes |-> NULL],
    mem = [n \in Nodes |-> NULL],
    node_cap = [n \in Nodes |-> NULL],
    p_rp0 = <<>>,
    c_rp0 = <<>>,
    n_rp0 = <<>>;

define
   Completion == (completeInstall) ~> <>[](useService) 
end define;

macro checkIsolation(node) begin \* TODO: Needs fixing according to cap-mem func
    with rp_set = rp[node] do
        with n \in Nodes \ {node} do
             assert rp[n] \intersect rp_set = {}; 
        end with;
    end with;
end macro;

macro secureProvider() begin
    \* wrap c_rp0 in mem
    p_rp0 := Append(p_rp0, [cap |-> c_rp0, mem |-> cmem]);
    c_rp0 := Append(c_rp0, [cap |-> NewNode, mem |-> cmem]);
    requestInstall := TRUE;
end macro; 

macro installService(node) begin
    checkIsolation(node);
end macro;

macro sendBack(new_rp) begin
    c_rp0 := Append(c_rp0, new_rp);
end macro;

macro checkService(node) begin
    checkIsolation(node);
    useService := TRUE;
end macro;

procedure resetNode(node) begin
Reset:
    with n \in Nodes \ {node} do
        rp[n] := rp[n] \ rp[node];
    end with;
return;
end procedure;

procedure revokeMem(membrane) begin \* TODO: Needs fixing according to cap-mem func
Revoke:
    with n \in Nodes \ {self} do
        rp[n] := rp[n] \ rp[node];
    end with;
return;
end procedure;

fair process client = Consumer
variables
    recv_rp
begin
    Start_c:
        rp[Consumer] := {[cap |-> c_rp0, mem |-> NULL], [cap |-> p_rp0, mem |-> NULL]} ||
        rp[NewNode] := {[cap |-> n_rp0, mem |-> NULL]};
        mem[Consumer] := {cmem};
        node_cap[Consumer] := {[cap |-> NewNode, mem |-> NULL]};
        secureProvider();
    WaitForService:
        await completeInstall /\ c_rp0 /= <<>>;
    Service:
        while c_rp0 /= <<>> do
            rp[Consumer] := rp[Consumer] \union {Head(c_rp0)};
            recv_rp := Head(c_rp0).cap;
            c_rp0 := Tail(c_rp0);
            call revokeMem(mem[Consumer]);
            UseService:
                checkService(NewNode);
        end while;
end process;

fair process server = Provider
variables 
    new_rp, new_node, node_mem;
begin
    Start_p:
        rp[Provider] := {[cap |-> p_rp0, mem |-> NULL]};
        await requestInstall;
    Install:
        await p_rp0 /= <<>>;
        rp[Provider] := rp[Provider] \union {Head(p_rp0)};
        new_rp := Head(p_rp0).cap;
        p_rp0 := Tail(p_rp0);
        await new_rp /= <<>>;
    GetCap:
        while new_rp /= <<>> do
            new_node := Head(new_rp).cap;
            call resetNode(new_node);
            StartInstall:
                node_mem := Head(new_rp);
                node_cap[Provider] := node_cap[Provider] \union {node_mem};
                new_rp := Tail(new_rp);
                rp[Provider] := rp[Provider] \union {[cap |-> n_rp0, mem |-> node_mem.mem]}; 
                installService(new_node);
                sendBack([cap |-> n_rp0, mem |-> NULL]); 
                completeInstall := TRUE;
        end while;
end process; 

end algorithm;*)

\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES Nodes, AllMem, requestInstall, completeInstall, useService, rp, mem, 
          node_cap, p_rp0, c_rp0, n_rp0, pc, stack

(* define statement *)
Completion == (completeInstall) ~> <>[](useService)

VARIABLES node, recv_rp, new_rp, new_node, node_mem

vars == << Nodes, AllMem, requestInstall, completeInstall, useService, rp, 
           mem, node_cap, p_rp0, c_rp0, n_rp0, pc, stack, node, recv_rp, 
           new_rp, new_node, node_mem >>

ProcSet == {Consumer} \cup {Provider}

Init == (* Global variables *)
        /\ Nodes = {Consumer, Provider, NewNode}
        /\ AllMem = {cmem}
        /\ requestInstall = FALSE
        /\ completeInstall = FALSE
        /\ useService = FALSE
        /\ rp = [n \in Nodes |-> NULL]
        /\ mem = [n \in Nodes |-> NULL]
        /\ node_cap = [n \in Nodes |-> NULL]
        /\ p_rp0 = <<>>
        /\ c_rp0 = <<>>
        /\ n_rp0 = <<>>
        (* Procedure resetNode *)
        /\ node = [ self \in ProcSet |-> defaultInitValue]
        (* Process client *)
        /\ recv_rp = defaultInitValue
        (* Process server *)
        /\ new_rp = defaultInitValue
        /\ new_node = defaultInitValue
        /\ node_mem = defaultInitValue
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = Consumer -> "Start_c"
                                        [] self = Provider -> "Start_p"]

Reset(self) == /\ pc[self] = "Reset"
               /\ \E n \in Nodes \ {node[self]}:
                    rp' = [rp EXCEPT ![n] = rp[n] \ rp[node[self]]]
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ node' = [node EXCEPT ![self] = Head(stack[self]).node]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << Nodes, AllMem, requestInstall, completeInstall, 
                               useService, mem, node_cap, p_rp0, c_rp0, n_rp0, 
                               recv_rp, new_rp, new_node, node_mem >>

resetNode(self) == Reset(self)

Start_c == /\ pc[Consumer] = "Start_c"
           /\ rp' = [rp EXCEPT ![Consumer] = {[cap |-> c_rp0, mem |-> NULL], [cap |-> p_rp0, mem |-> NULL]},
                               ![NewNode] = {[cap |-> n_rp0, mem |-> NULL]}]
           /\ mem' = [mem EXCEPT ![Consumer] = {cmem}]
           /\ node_cap' = [node_cap EXCEPT ![Consumer] = {[cap |-> NewNode, mem |-> NULL]}]
           /\ p_rp0' = Append(p_rp0, [cap |-> c_rp0, mem |-> cmem])
           /\ c_rp0' = Append(c_rp0, [cap |-> NewNode, mem |-> cmem])
           /\ requestInstall' = TRUE
           /\ pc' = [pc EXCEPT ![Consumer] = "WaitForService"]
           /\ UNCHANGED << Nodes, AllMem, completeInstall, useService, n_rp0, 
                           stack, node, recv_rp, new_rp, new_node, node_mem >>

WaitForService == /\ pc[Consumer] = "WaitForService"
                  /\ completeInstall /\ c_rp0 /= <<>>
                  /\ pc' = [pc EXCEPT ![Consumer] = "Service"]
                  /\ UNCHANGED << Nodes, AllMem, requestInstall, 
                                  completeInstall, useService, rp, mem, 
                                  node_cap, p_rp0, c_rp0, n_rp0, stack, node, 
                                  recv_rp, new_rp, new_node, node_mem >>

Service == /\ pc[Consumer] = "Service"
           /\ IF c_rp0 /= <<>>
                 THEN /\ recv_rp' = Head(c_rp0)
                      /\ c_rp0' = Tail(c_rp0)
                      /\ rp' = [rp EXCEPT ![Consumer] = rp[Consumer] \union {recv_rp'}]
                      /\ /\ node' = [node EXCEPT ![Consumer] = node[Consumer]]
                         /\ stack' = [stack EXCEPT ![Consumer] = << [ procedure |->  "resetNode",
                                                                      pc        |->  "UseService",
                                                                      node      |->  node[Consumer] ] >>
                                                                  \o stack[Consumer]]
                      /\ pc' = [pc EXCEPT ![Consumer] = "Reset"]
                 ELSE /\ pc' = [pc EXCEPT ![Consumer] = "Done"]
                      /\ UNCHANGED << rp, c_rp0, stack, node, recv_rp >>
           /\ UNCHANGED << Nodes, AllMem, requestInstall, completeInstall, 
                           useService, mem, node_cap, p_rp0, n_rp0, new_rp, 
                           new_node, node_mem >>

UseService == /\ pc[Consumer] = "UseService"
              /\ LET rp_set == rp[NewNode] IN
                   \E n \in Nodes \ {NewNode}:
                     Assert(rp[n] \intersect rp_set = {}, 
                            "Failure of assertion at line 27, column 14 of macro called at line 79, column 17.")
              /\ useService' = TRUE
              /\ pc' = [pc EXCEPT ![Consumer] = "Service"]
              /\ UNCHANGED << Nodes, AllMem, requestInstall, completeInstall, 
                              rp, mem, node_cap, p_rp0, c_rp0, n_rp0, stack, 
                              node, recv_rp, new_rp, new_node, node_mem >>

client == Start_c \/ WaitForService \/ Service \/ UseService

Start_p == /\ pc[Provider] = "Start_p"
           /\ rp' = [rp EXCEPT ![Provider] = {[cap |-> p_rp0, mem |-> NULL]}]
           /\ requestInstall
           /\ pc' = [pc EXCEPT ![Provider] = "Install"]
           /\ UNCHANGED << Nodes, AllMem, requestInstall, completeInstall, 
                           useService, mem, node_cap, p_rp0, c_rp0, n_rp0, 
                           stack, node, recv_rp, new_rp, new_node, node_mem >>

Install == /\ pc[Provider] = "Install"
           /\ p_rp0 /= <<>>
           /\ rp' = [rp EXCEPT ![Provider] = rp[Provider] \union {Head(p_rp0)}]
           /\ new_rp' = Head(p_rp0).cap
           /\ p_rp0' = Tail(p_rp0)
           /\ new_rp' /= <<>>
           /\ pc' = [pc EXCEPT ![Provider] = "GetCap"]
           /\ UNCHANGED << Nodes, AllMem, requestInstall, completeInstall, 
                           useService, mem, node_cap, c_rp0, n_rp0, stack, 
                           node, recv_rp, new_node, node_mem >>

GetCap == /\ pc[Provider] = "GetCap"
          /\ IF new_rp /= <<>>
                THEN /\ new_node' = Head(new_rp).cap
                     /\ /\ node' = [node EXCEPT ![Provider] = new_node']
                        /\ stack' = [stack EXCEPT ![Provider] = << [ procedure |->  "resetNode",
                                                                     pc        |->  "StartInstall",
                                                                     node      |->  node[Provider] ] >>
                                                                 \o stack[Provider]]
                     /\ pc' = [pc EXCEPT ![Provider] = "Reset"]
                ELSE /\ pc' = [pc EXCEPT ![Provider] = "Done"]
                     /\ UNCHANGED << stack, node, new_node >>
          /\ UNCHANGED << Nodes, AllMem, requestInstall, completeInstall, 
                          useService, rp, mem, node_cap, p_rp0, c_rp0, n_rp0, 
                          recv_rp, new_rp, node_mem >>

StartInstall == /\ pc[Provider] = "StartInstall"
                /\ node_mem' = Head(new_rp)
                /\ node_cap' = [node_cap EXCEPT ![Provider] = node_cap[Provider] \union {node_mem'}]
                /\ new_rp' = Tail(new_rp)
                /\ rp' = [rp EXCEPT ![Provider] = rp[Provider] \union {[cap |-> n_rp0, mem |-> node_mem'.mem]}]
                /\ LET rp_set == rp'[new_node] IN
                     \E n \in Nodes \ {new_node}:
                       Assert(rp'[n] \intersect rp_set = {}, 
                              "Failure of assertion at line 27, column 14 of macro called at line 105, column 17.")
                /\ c_rp0' = Append(c_rp0, ([cap |-> n_rp0, mem |-> NULL]))
                /\ completeInstall' = TRUE
                /\ pc' = [pc EXCEPT ![Provider] = "GetCap"]
                /\ UNCHANGED << Nodes, AllMem, requestInstall, useService, mem, 
                                p_rp0, n_rp0, stack, node, recv_rp, new_node >>

server == Start_p \/ Install \/ GetCap \/ StartInstall

Next == client \/ server
           \/ (\E self \in ProcSet: resetNode(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(client) /\ WF_vars(resetNode(Consumer))
        /\ WF_vars(server) /\ WF_vars(resetNode(Provider))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Wed Dec 19 11:41:44 MST 2018 by aarushi
\* Created Mon Nov 05 10:01:52 MST 2018 by aarushi
