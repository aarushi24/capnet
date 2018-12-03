--------------------------- MODULE SecureProvider ---------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT NULL, Consumer, Provider, NewNode

(*--algorithm secureProvider
variables
    Nodes = {Consumer, Provider, NewNode},
    requestInstall = FALSE, 
    startInstall = FALSE, 
    completeInstall = FALSE,
    useService = FALSE,
    rp = [n \in Nodes |-> NULL],
    mem = [n \in Nodes |-> NULL],
    node_cap = [n \in Nodes |-> NULL],
    p_rp0 = <<>>,
    c_rp0 = <<>>;

define
   Completion == (completeInstall) ~> <>[](useService) 
end define;

macro checkIsolation(node) begin
    with rp_set = rp[node] do
        with n \in Nodes \ {node} do
             assert rp[n] \intersect rp_set = {}; 
        end with;
    end with;
end macro;

macro secureProvider() begin
    \* TODO: wrap c_rp0 in mem
    p_rp0 := Append(p_rp0, c_rp0);
    c_rp0 := Append(c_rp0, NewNode);
    requestInstall := TRUE;
end macro; 

(*macro resetNode(node) begin
    with n \in Nodes \ {node} do
        rp[n] := rp[n] \ rp[node];
    end with;
end macro;*)

macro installService(node) begin
    checkIsolation(node);
    startInstall := TRUE;
end macro;

macro sendBack(node) begin
    c_rp0 := Append(c_rp0, node);
end macro;

macro checkService(node) begin
    \*resetNode(node);
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

fair process client = Consumer
begin
    Start_c:
        rp[Consumer] := {c_rp0, p_rp0};
        mem[Consumer] := {"mem"};
        node_cap[Consumer] := {NewNode};
        \*rp[NewNode] := {"n_rp0"};
        secureProvider();
        goto Service;
    Service:
        await completeInstall /\ c_rp0 /= <<>>;
        with recv_node = Head(c_rp0) do
            node_cap[Consumer] := node_cap[Consumer] \union {recv_node};
            checkService(recv_node);
        end with;
end process;

fair process server = Provider
begin
    Start_p:
        rp[Provider] := {p_rp0};
        await requestInstall;
        goto Install;
    Install:
        await p_rp0 /= <<>>;
        with new_rp = Head(p_rp0) do 
            rp[Provider] := rp[Provider] \union {new_rp};
            await new_rp /= <<>>;
            \*while new_rp /= <<>> do
            with new_node = Head(new_rp) do
                node_cap[Provider] := node_cap[Provider] \union {new_node};
                \*call resetNode(new_node);
                \*rp[Provider] := rp[Provider] \union {"n_rp0"};
                installService(new_node);
                sendBack(new_node); \* TODO: Send back RP not node!
                completeInstall := TRUE;
            end with;
        end with;
end process; 

end algorithm;*)

\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES Nodes, requestInstall, startInstall, completeInstall, useService, 
          rp, mem, node_cap, p_rp0, c_rp0, pc, stack

(* define statement *)
Completion == (completeInstall) ~> <>[](useService)

VARIABLE node

vars == << Nodes, requestInstall, startInstall, completeInstall, useService, 
           rp, mem, node_cap, p_rp0, c_rp0, pc, stack, node >>

ProcSet == {Consumer} \cup {Provider}

Init == (* Global variables *)
        /\ Nodes = {Consumer, Provider, NewNode}
        /\ requestInstall = FALSE
        /\ startInstall = FALSE
        /\ completeInstall = FALSE
        /\ useService = FALSE
        /\ rp = [n \in Nodes |-> NULL]
        /\ mem = [n \in Nodes |-> NULL]
        /\ node_cap = [n \in Nodes |-> NULL]
        /\ p_rp0 = <<>>
        /\ c_rp0 = <<>>
        (* Procedure resetNode *)
        /\ node = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = Consumer -> "Start_c"
                                        [] self = Provider -> "Start_p"]

Reset(self) == /\ pc[self] = "Reset"
               /\ \E n \in Nodes \ {node[self]}:
                    rp' = [rp EXCEPT ![n] = rp[n] \ rp[node[self]]]
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ node' = [node EXCEPT ![self] = Head(stack[self]).node]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << Nodes, requestInstall, startInstall, 
                               completeInstall, useService, mem, node_cap, 
                               p_rp0, c_rp0 >>

resetNode(self) == Reset(self)

Start_c == /\ pc[Consumer] = "Start_c"
           /\ rp' = [rp EXCEPT ![Consumer] = {c_rp0, p_rp0}]
           /\ mem' = [mem EXCEPT ![Consumer] = {"mem"}]
           /\ node_cap' = [node_cap EXCEPT ![Consumer] = {NewNode}]
           /\ p_rp0' = Append(p_rp0, c_rp0)
           /\ c_rp0' = Append(c_rp0, NewNode)
           /\ requestInstall' = TRUE
           /\ pc' = [pc EXCEPT ![Consumer] = "Service"]
           /\ UNCHANGED << Nodes, startInstall, completeInstall, useService, 
                           stack, node >>

Service == /\ pc[Consumer] = "Service"
           /\ completeInstall /\ c_rp0 /= <<>>
           /\ LET recv_node == Head(c_rp0) IN
                /\ node_cap' = [node_cap EXCEPT ![Consumer] = node_cap[Consumer] \union {recv_node}]
                /\ LET rp_set == rp[recv_node] IN
                     \E n \in Nodes \ {recv_node}:
                       Assert(rp[n] \intersect rp_set = {}, 
                              "Failure of assertion at line 26, column 14 of macro called at line 80, column 13.")
                /\ useService' = TRUE
           /\ pc' = [pc EXCEPT ![Consumer] = "Done"]
           /\ UNCHANGED << Nodes, requestInstall, startInstall, 
                           completeInstall, rp, mem, p_rp0, c_rp0, stack, node >>

client == Start_c \/ Service

Start_p == /\ pc[Provider] = "Start_p"
           /\ rp' = [rp EXCEPT ![Provider] = {p_rp0}]
           /\ requestInstall
           /\ pc' = [pc EXCEPT ![Provider] = "Install"]
           /\ UNCHANGED << Nodes, requestInstall, startInstall, 
                           completeInstall, useService, mem, node_cap, p_rp0, 
                           c_rp0, stack, node >>

Install == /\ pc[Provider] = "Install"
           /\ p_rp0 /= <<>>
           /\ LET new_rp == Head(p_rp0) IN
                /\ rp' = [rp EXCEPT ![Provider] = rp[Provider] \union {new_rp}]
                /\ new_rp /= <<>>
                /\ LET new_node == Head(new_rp) IN
                     /\ node_cap' = [node_cap EXCEPT ![Provider] = node_cap[Provider] \union {new_node}]
                     /\ LET rp_set == rp'[new_node] IN
                          \E n \in Nodes \ {new_node}:
                            Assert(rp'[n] \intersect rp_set = {}, 
                                   "Failure of assertion at line 26, column 14 of macro called at line 100, column 17.")
                     /\ startInstall' = TRUE
                     /\ c_rp0' = Append(c_rp0, new_node)
                     /\ completeInstall' = TRUE
           /\ pc' = [pc EXCEPT ![Provider] = "Done"]
           /\ UNCHANGED << Nodes, requestInstall, useService, mem, p_rp0, 
                           stack, node >>

server == Start_p \/ Install

Next == client \/ server
           \/ (\E self \in ProcSet: resetNode(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(client)
        /\ WF_vars(server)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Mon Dec 03 15:02:49 MST 2018 by aarushi
\* Created Mon Nov 05 10:01:52 MST 2018 by aarushi
