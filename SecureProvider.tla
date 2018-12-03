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
    mem = [n \in Nodes |-> NULL];

define
   Completion == (completeInstall) ~> <>[](useService) 
end define;

macro checkIsolation(node) begin
    with rp_set = rp[node] \intersect {"p_rp0"} do
        with n \in Nodes \ {node} do
             assert rp[n] \intersect rp_set = {}; 
        end with;
    end with;
end macro;

macro secureProvider() begin
    requestInstall := TRUE;
end macro; 

macro installService() begin
    checkIsolation(Consumer);
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
        rp[Consumer] := {"c_rp0", "p_rp0"};
        mem[Consumer] := {"mem"};
        secureProvider();
        await completeInstall;
        checkService();
end process;

fair process server = Provider
begin
    Start_p:
        rp[Provider] := {"p_rp0"};
        await requestInstall;
        installService();
        sendBack();
end process; 

end algorithm;*)

\* BEGIN TRANSLATION
VARIABLES Nodes, requestInstall, startInstall, completeInstall, useService, 
          rp, mem, pc

(* define statement *)
Completion == (completeInstall) ~> <>[](useService)


vars == << Nodes, requestInstall, startInstall, completeInstall, useService, 
           rp, mem, pc >>

ProcSet == {Consumer} \cup {Provider}

Init == (* Global variables *)
        /\ Nodes = {Consumer, Provider}
        /\ requestInstall = FALSE
        /\ startInstall = FALSE
        /\ completeInstall = FALSE
        /\ useService = FALSE
        /\ rp = [n \in Nodes |-> NULL]
        /\ mem = [n \in Nodes |-> NULL]
        /\ pc = [self \in ProcSet |-> CASE self = Consumer -> "Start_c"
                                        [] self = Provider -> "Start_p"]

Start_c == /\ pc[Consumer] = "Start_c"
           /\ rp' = [rp EXCEPT ![Consumer] = {"c_rp0", "p_rp0"}]
           /\ mem' = [mem EXCEPT ![Consumer] = {"mem"}]
           /\ requestInstall' = TRUE
           /\ completeInstall
           /\ LET rp_set == rp'[Provider] \intersect {"p_rp0"} IN
                \E n \in Nodes \ {Provider}:
                  Assert(rp'[n] \intersect rp_set = {}, 
                         "Failure of assertion at line 23, column 14 of macro called at line 53, column 9.")
           /\ useService' = TRUE
           /\ pc' = [pc EXCEPT ![Consumer] = "Done"]
           /\ UNCHANGED << Nodes, startInstall, completeInstall >>

client == Start_c

Start_p == /\ pc[Provider] = "Start_p"
           /\ rp' = [rp EXCEPT ![Provider] = {"p_rp0"}]
           /\ requestInstall
           /\ LET rp_set == rp'[Consumer] \intersect {"p_rp0"} IN
                \E n \in Nodes \ {Consumer}:
                  Assert(rp'[n] \intersect rp_set = {}, 
                         "Failure of assertion at line 23, column 14 of macro called at line 61, column 9.")
           /\ startInstall' = TRUE
           /\ completeInstall' = TRUE
           /\ pc' = [pc EXCEPT ![Provider] = "Done"]
           /\ UNCHANGED << Nodes, requestInstall, useService, mem >>

server == Start_p

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
\* Last modified Sun Dec 02 21:07:44 MST 2018 by aarushi
\* Created Mon Nov 05 10:01:52 MST 2018 by aarushi
