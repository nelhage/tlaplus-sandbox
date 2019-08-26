---- MODULE lamport_clock ----
EXTENDS Integers, TLC

(* --algorithm manage_clock
variables nproc = 2,
  Processes = 1..nproc,
  Steps = 4,
  Tick = 0,
  Counters = [proc \in 1..nproc |-> 0];

begin
  A: with proc \in Processes do
    print proc;
  end with;
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES nproc, Processes, Steps, Tick, Counters, pc

vars == << nproc, Processes, Steps, Tick, Counters, pc >>

Init == (* Global variables *)
        /\ nproc = 2
        /\ Processes = 1..nproc
        /\ Steps = 4
        /\ Tick = 0
        /\ Counters = [proc \in 1..nproc |-> 0]
        /\ pc = "A"

A == /\ pc = "A"
     /\ \E proc \in Processes:
          PrintT(proc)
     /\ pc' = "Done"
     /\ UNCHANGED << nproc, Processes, Steps, Tick, Counters >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == A
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
====
