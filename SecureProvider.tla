--------------------------- MODULE SecureProvider ---------------------------
EXTENDS TLC, Integers, Sequences

CONSTANT NULL, Consumer, Provider

(*--algorithm secureProvider
variables
    Nodes = {Consumer, Provider},
    requestInstall = FALSE, 
    startInstall = FALSE, 
    completeInstall = FALSE,
    useService = FALSE;
    isolation = [n \in Nodes |-> FALSE]

procedure secureProvider() begin
Start:
    isolation[self] := TRUE;
    requestInstall := TRUE;
end procedure; 

procedure installService() begin
Start:
    assert isolation[Consumer];
    startInstall := TRUE;
end procedure;

procedure sendBack() begin
Start:
    isolation[self] := TRUE;
    completeInstall := TRUE;
end procedure;

procedure checkService() begin
Start:
    assert isolation[Provider]; \* This should be of the nodes sent back
    useService := TRUE;
end procedure;

process client = Consumer
begin
    Start:
        call secureProvider();
    Complete:
        await completeInstall;
        call checkService();
end process;

process server = Provider
begin
    Start:
        await requestInstall;
        call installService();
    Return:
        call sendBack();
end process; 

end algorithm;*)

\* BEGIN TRANSLATION
\* Label Start of procedure secureProvider at line 17 col 5 changed to Start_
\* Label Start of procedure installService at line 23 col 5 changed to Start_i
\* Label Start of procedure sendBack at line 29 col 5 changed to Start_s
\* Label Start of procedure checkService at line 35 col 5 changed to Start_c
\* Label Start of process client at line 42 col 9 changed to Start_cl
VARIABLES Nodes, requestInstall, startInstall, completeInstall, useService, 
          isolation, pc, stack

vars == << Nodes, requestInstall, startInstall, completeInstall, useService, 
           isolation, pc, stack >>

ProcSet == {Consumer} \cup {Provider}

Init == (* Global variables *)
        /\ Nodes = {Consumer, Provider}
        /\ requestInstall = FALSE
        /\ startInstall = FALSE
        /\ completeInstall = FALSE
        /\ useService = FALSE
        /\ isolation = [n \in Nodes |-> FALSE]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = Consumer -> "Start_cl"
                                        [] self = Provider -> "Start"]

Start_(self) == /\ pc[self] = "Start_"
                /\ isolation' = [isolation EXCEPT ![self] = TRUE]
                /\ requestInstall' = TRUE
                /\ pc' = [pc EXCEPT ![self] = "Error"]
                /\ UNCHANGED << Nodes, startInstall, completeInstall, 
                                useService, stack >>

secureProvider(self) == Start_(self)

Start_i(self) == /\ pc[self] = "Start_i"
                 /\ Assert(isolation[Consumer], 
                           "Failure of assertion at line 23, column 5.")
                 /\ startInstall' = TRUE
                 /\ pc' = [pc EXCEPT ![self] = "Error"]
                 /\ UNCHANGED << Nodes, requestInstall, completeInstall, 
                                 useService, isolation, stack >>

installService(self) == Start_i(self)

Start_s(self) == /\ pc[self] = "Start_s"
                 /\ isolation' = [isolation EXCEPT ![self] = TRUE]
                 /\ completeInstall' = TRUE
                 /\ pc' = [pc EXCEPT ![self] = "Error"]
                 /\ UNCHANGED << Nodes, requestInstall, startInstall, 
                                 useService, stack >>

sendBack(self) == Start_s(self)

Start_c(self) == /\ pc[self] = "Start_c"
                 /\ Assert(isolation[Provider], 
                           "Failure of assertion at line 35, column 5.")
                 /\ useService' = TRUE
                 /\ pc' = [pc EXCEPT ![self] = "Error"]
                 /\ UNCHANGED << Nodes, requestInstall, startInstall, 
                                 completeInstall, isolation, stack >>

checkService(self) == Start_c(self)

Start_cl == /\ pc[Consumer] = "Start_cl"
            /\ stack' = [stack EXCEPT ![Consumer] = << [ procedure |->  "secureProvider",
                                                         pc        |->  "Complete" ] >>
                                                     \o stack[Consumer]]
            /\ pc' = [pc EXCEPT ![Consumer] = "Start_"]
            /\ UNCHANGED << Nodes, requestInstall, startInstall, 
                            completeInstall, useService, isolation >>

Complete == /\ pc[Consumer] = "Complete"
            /\ completeInstall
            /\ stack' = [stack EXCEPT ![Consumer] = << [ procedure |->  "checkService",
                                                         pc        |->  "Done" ] >>
                                                     \o stack[Consumer]]
            /\ pc' = [pc EXCEPT ![Consumer] = "Start_c"]
            /\ UNCHANGED << Nodes, requestInstall, startInstall, 
                            completeInstall, useService, isolation >>

client == Start_cl \/ Complete

Start == /\ pc[Provider] = "Start"
         /\ requestInstall
         /\ stack' = [stack EXCEPT ![Provider] = << [ procedure |->  "installService",
                                                      pc        |->  "Return" ] >>
                                                  \o stack[Provider]]
         /\ pc' = [pc EXCEPT ![Provider] = "Start_i"]
         /\ UNCHANGED << Nodes, requestInstall, startInstall, completeInstall, 
                         useService, isolation >>

Return == /\ pc[Provider] = "Return"
          /\ stack' = [stack EXCEPT ![Provider] = << [ procedure |->  "sendBack",
                                                       pc        |->  "Done" ] >>
                                                   \o stack[Provider]]
          /\ pc' = [pc EXCEPT ![Provider] = "Start_s"]
          /\ UNCHANGED << Nodes, requestInstall, startInstall, completeInstall, 
                          useService, isolation >>

server == Start \/ Return

Next == client \/ server
           \/ (\E self \in ProcSet:  \/ secureProvider(self)
                                     \/ installService(self) \/ sendBack(self)
                                     \/ checkService(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sun Dec 02 16:21:13 MST 2018 by aarushi
\* Created Mon Nov 05 10:01:52 MST 2018 by aarushi
