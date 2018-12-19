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
    n_rp0 = <<>>;

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

fair process client = Consumer
variables
    recv_rp
begin
    Start_c:
        rp[Consumer] := {c_rp0, p_rp0} ||
        rp[NewNode] := {n_rp0};
        mem[Consumer] := {"c_mem"};
        node_cap[Consumer] := {NewNode};
        secureProvider();
    WaitForService:
        await completeInstall /\ c_rp0 /= <<>>;
    Service:
        while c_rp0 /= <<>> do
            recv_rp := Head(c_rp0);
            c_rp0 := Tail(c_rp0);
            rp[Consumer] := rp[Consumer] \union {recv_rp};
            call resetNode(node);
            UseService:
                checkService(NewNode);
        end while;
end process;

fair process server = Provider
variables 
    new_rp, new_node;
begin
    Start_p:
        rp[Provider] := {p_rp0};
        await requestInstall;
    Install:
        await p_rp0 /= <<>>;
        new_rp := Head(p_rp0);
        p_rp0 := Tail(p_rp0);
        rp[Provider] := rp[Provider] \union {new_rp};
        await new_rp /= <<>>;
    GetCap:
        while new_rp /= <<>> do
            new_node := Head(new_rp);
            new_rp := Tail(new_rp);
            call resetNode(new_node);
            StartInstall:
                node_cap[Provider] := node_cap[Provider] \union {new_node};
                rp[Provider] := rp[Provider] \union {n_rp0};
                installService(new_node);
                sendBack(n_rp0); 
                completeInstall := TRUE;
        end while;
end process; 

end algorithm;*)

\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES Nodes, requestInstall, startInstall, completeInstall, useService, 
          rp, mem, node_cap, p_rp0, c_rp0, n_rp0, pc, stack

(* define statement *)
Completion == (completeInstall) ~> <>[](useService)

VARIABLES node, recv_rp, new_rp, new_node

vars == << Nodes, requestInstall, startInstall, completeInstall, useService, 
           rp, mem, node_cap, p_rp0, c_rp0, n_rp0, pc, stack, node, recv_rp, 
           new_rp, new_node >>

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
        /\ n_rp0 = <<>>
        (* Procedure resetNode *)
        /\ node = [ self \in ProcSet |-> defaultInitValue]
        (* Process client *)
        /\ recv_rp = defaultInitValue
        (* Process server *)
        /\ new_rp = defaultInitValue
        /\ new_node = defaultInitValue
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
                               p_rp0, c_rp0, n_rp0, recv_rp, new_rp, new_node >>

resetNode(self) == Reset(self)

Start_c == /\ pc[Consumer] = "Start_c"
           /\ rp' = [rp EXCEPT ![Consumer] = {c_rp0, p_rp0},
                               ![NewNode] = {n_rp0}]
           /\ mem' = [mem EXCEPT ![Consumer] = {"c_mem"}]
           /\ node_cap' = [node_cap EXCEPT ![Consumer] = {NewNode}]
           /\ p_rp0' = Append(p_rp0, c_rp0)
           /\ c_rp0' = Append(c_rp0, NewNode)
           /\ requestInstall' = TRUE
           /\ pc' = [pc EXCEPT ![Consumer] = "WaitForService"]
           /\ UNCHANGED << Nodes, startInstall, completeInstall, useService, 
                           n_rp0, stack, node, recv_rp, new_rp, new_node >>

WaitForService == /\ pc[Consumer] = "WaitForService"
                  /\ completeInstall /\ c_rp0 /= <<>>
                  /\ pc' = [pc EXCEPT ![Consumer] = "Service"]
                  /\ UNCHANGED << Nodes, requestInstall, startInstall, 
                                  completeInstall, useService, rp, mem, 
                                  node_cap, p_rp0, c_rp0, n_rp0, stack, node, 
                                  recv_rp, new_rp, new_node >>

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
           /\ UNCHANGED << Nodes, requestInstall, startInstall, 
                           completeInstall, useService, mem, node_cap, p_rp0, 
                           n_rp0, new_rp, new_node >>

UseService == /\ pc[Consumer] = "UseService"
              /\ LET rp_set == rp[NewNode] IN
                   \E n \in Nodes \ {NewNode}:
                     Assert(rp[n] \intersect rp_set = {}, 
                            "Failure of assertion at line 27, column 14 of macro called at line 86, column 17.")
              /\ useService' = TRUE
              /\ pc' = [pc EXCEPT ![Consumer] = "Service"]
              /\ UNCHANGED << Nodes, requestInstall, startInstall, 
                              completeInstall, rp, mem, node_cap, p_rp0, c_rp0, 
                              n_rp0, stack, node, recv_rp, new_rp, new_node >>

client == Start_c \/ WaitForService \/ Service \/ UseService

Start_p == /\ pc[Provider] = "Start_p"
           /\ rp' = [rp EXCEPT ![Provider] = {p_rp0}]
           /\ requestInstall
           /\ pc' = [pc EXCEPT ![Provider] = "Install"]
           /\ UNCHANGED << Nodes, requestInstall, startInstall, 
                           completeInstall, useService, mem, node_cap, p_rp0, 
                           c_rp0, n_rp0, stack, node, recv_rp, new_rp, 
                           new_node >>

Install == /\ pc[Provider] = "Install"
           /\ p_rp0 /= <<>>
           /\ new_rp' = Head(p_rp0)
           /\ p_rp0' = Tail(p_rp0)
           /\ rp' = [rp EXCEPT ![Provider] = rp[Provider] \union {new_rp'}]
           /\ new_rp' /= <<>>
           /\ pc' = [pc EXCEPT ![Provider] = "GetCap"]
           /\ UNCHANGED << Nodes, requestInstall, startInstall, 
                           completeInstall, useService, mem, node_cap, c_rp0, 
                           n_rp0, stack, node, recv_rp, new_node >>

GetCap == /\ pc[Provider] = "GetCap"
          /\ IF new_rp /= <<>>
                THEN /\ new_node' = Head(new_rp)
                     /\ new_rp' = Tail(new_rp)
                     /\ /\ node' = [node EXCEPT ![Provider] = new_node']
                        /\ stack' = [stack EXCEPT ![Provider] = << [ procedure |->  "resetNode",
                                                                     pc        |->  "StartInstall",
                                                                     node      |->  node[Provider] ] >>
                                                                 \o stack[Provider]]
                     /\ pc' = [pc EXCEPT ![Provider] = "Reset"]
                ELSE /\ pc' = [pc EXCEPT ![Provider] = "Done"]
                     /\ UNCHANGED << stack, node, new_rp, new_node >>
          /\ UNCHANGED << Nodes, requestInstall, startInstall, completeInstall, 
                          useService, rp, mem, node_cap, p_rp0, c_rp0, n_rp0, 
                          recv_rp >>

StartInstall == /\ pc[Provider] = "StartInstall"
                /\ node_cap' = [node_cap EXCEPT ![Provider] = node_cap[Provider] \union {new_node}]
                /\ rp' = [rp EXCEPT ![Provider] = rp[Provider] \union {n_rp0}]
                /\ LET rp_set == rp'[new_node] IN
                     \E n \in Nodes \ {new_node}:
                       Assert(rp'[n] \intersect rp_set = {}, 
                              "Failure of assertion at line 27, column 14 of macro called at line 111, column 17.")
                /\ startInstall' = TRUE
                /\ c_rp0' = Append(c_rp0, n_rp0)
                /\ completeInstall' = TRUE
                /\ pc' = [pc EXCEPT ![Provider] = "GetCap"]
                /\ UNCHANGED << Nodes, requestInstall, useService, mem, p_rp0, 
                                n_rp0, stack, node, recv_rp, new_rp, new_node >>

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
\* Last modified Wed Dec 19 08:59:35 MST 2018 by aarushi
\* Created Mon Nov 05 10:01:52 MST 2018 by aarushi
