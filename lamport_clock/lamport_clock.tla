---- MODULE lamport_clock ----
EXTENDS Integers, TLC

Max(x, y) == IF x < y THEN y ELSE x

(* --algorithm manage_clock
variables nproc = 2,
  Processes = 1..nproc,
  Steps = 4,
  Tick = 0,
  Counters = [proc \in Processes |-> 0],
  msgtime;

begin
  while Tick < Steps do
    with send \in Processes, recv \in Processes do
      \* print [tick |-> Tick, from |-> send, to |-> rcv];
      msgtime := Counters[send] + 1;
      Counters[send] := msgtime ||
      Counters[recv] := Max(msgtime, Counters[recv]) + 1;
    end with;

    Tick := Tick + 1;
  end while;
end algorithm; *)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES nproc, Processes, Steps, Tick, Counters, msgtime, pc

vars == << nproc, Processes, Steps, Tick, Counters, msgtime, pc >>

Init == (* Global variables *)
        /\ nproc = 2
        /\ Processes = 1..nproc
        /\ Steps = 4
        /\ Tick = 0
        /\ Counters = [proc \in Processes |-> 0]
        /\ msgtime = defaultInitValue
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF Tick < Steps
               THEN /\ \E send \in Processes:
                         \E recv \in Processes:
                           /\ msgtime' = Counters[send] + 1
                           /\ Counters' = [Counters EXCEPT ![send] = msgtime',
                                                           ![recv] = Max(msgtime', Counters[recv]) + 1]
                    /\ Tick' = Tick + 1
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << Tick, Counters, msgtime >>
         /\ UNCHANGED << nproc, Processes, Steps >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
====
