--------------------------- MODULE SecureProvider ---------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT NULL, Consumer, Provider

(*--algorithm secureProvider
variables
    Nodes = {Consumer, Provider},
    requestInstall = FALSE, 
    startInstall = FALSE, 
    completeInstall = FALSE,
    useService = FALSE,
    rp = [n \in Nodes |-> NULL],
    mem = [n \in Nodes |-> NULL],
    p_rp0 = <<>>,
    c_rp0 = <<>>;

define
   Completion == (completeInstall) ~> <>[](useService) 
end define;

macro checkIsolation(node) begin
    with rp_set = rp[node] \intersect {p_rp0} do
        with n \in Nodes \ {node} do
             assert rp[n] \intersect rp_set = {}; 
        end with;
    end with;
end macro;

macro recv(node, queue) begin
    
end macro;

macro secureProvider() begin
    \* TODO: wrap c_rp0 in mem
    p_rp0 := Append(p_rp0, c_rp0);
    requestInstall := TRUE;
end macro; 

macro installService() begin
    \*checkIsolation(NewNode);
    startInstall := TRUE;
end macro;

macro sendBack() begin
    completeInstall := TRUE;
end macro;

macro checkService() begin
    checkIsolation(Provider);
    useService := TRUE;
end macro;

fair process client = Consumer
begin
    Start_c:
        rp[Consumer] := {c_rp0, p_rp0};
        mem[Consumer] := {"mem"};
        secureProvider();
        await completeInstall;
        checkService();
end process;

fair process server = Provider
begin
    Start_p:
        rp[Provider] := {p_rp0};
        await requestInstall;
        goto Install;
    Install:
        await p_rp0 /= <<>>;
        rp[Provider] := rp[Provider] \union {Head(p_rp0)};
        installService();
        sendBack();
end process; 

end algorithm;*)

\* BEGIN TRANSLATION
VARIABLES Nodes, requestInstall, startInstall, completeInstall, useService, 
          rp, mem, p_rp0, c_rp0, pc

(* define statement *)
Completion == (completeInstall) ~> <>[](useService)


vars == << Nodes, requestInstall, startInstall, completeInstall, useService, 
           rp, mem, p_rp0, c_rp0, pc >>

ProcSet == {Consumer} \cup {Provider}

Init == (* Global variables *)
        /\ Nodes = {Consumer, Provider}
        /\ requestInstall = FALSE
        /\ startInstall = FALSE
        /\ completeInstall = FALSE
        /\ useService = FALSE
        /\ rp = [n \in Nodes |-> NULL]
        /\ mem = [n \in Nodes |-> NULL]
        /\ p_rp0 = <<>>
        /\ c_rp0 = <<>>
        /\ pc = [self \in ProcSet |-> CASE self = Consumer -> "Start_c"
                                        [] self = Provider -> "Start_p"]

Start_c == /\ pc[Consumer] = "Start_c"
           /\ rp' = [rp EXCEPT ![Consumer] = {c_rp0, p_rp0}]
           /\ mem' = [mem EXCEPT ![Consumer] = {"mem"}]
           /\ p_rp0' = Append(p_rp0, c_rp0)
           /\ requestInstall' = TRUE
           /\ completeInstall
           /\ LET rp_set == rp'[Provider] \intersect {p_rp0'} IN
                \E n \in Nodes \ {Provider}:
                  Assert(rp'[n] \intersect rp_set = {}, 
                         "Failure of assertion at line 25, column 14 of macro called at line 61, column 9.")
           /\ useService' = TRUE
           /\ pc' = [pc EXCEPT ![Consumer] = "Done"]
           /\ UNCHANGED << Nodes, startInstall, completeInstall, c_rp0 >>

client == Start_c

Start_p == /\ pc[Provider] = "Start_p"
           /\ rp' = [rp EXCEPT ![Provider] = {p_rp0}]
           /\ requestInstall
           /\ pc' = [pc EXCEPT ![Provider] = "Install"]
           /\ UNCHANGED << Nodes, requestInstall, startInstall, 
                           completeInstall, useService, mem, p_rp0, c_rp0 >>

Install == /\ pc[Provider] = "Install"
           /\ p_rp0 /= <<>>
           /\ rp' = [rp EXCEPT ![Provider] = rp[Provider] \union {Head(p_rp0)}]
           /\ startInstall' = TRUE
           /\ completeInstall' = TRUE
           /\ pc' = [pc EXCEPT ![Provider] = "Done"]
           /\ UNCHANGED << Nodes, requestInstall, useService, mem, p_rp0, 
                           c_rp0 >>

server == Start_p \/ Install

Next == client \/ server
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(client)
        /\ WF_vars(server)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Mon Dec 03 12:21:50 MST 2018 by aarushi
\* Created Mon Nov 05 10:01:52 MST 2018 by aarushi
