---- MODULE lamport_clock ----
EXTENDS Integers, TLC, FiniteSets
CONSTANT Steps, Processes

ASSUME Steps \in Nat \ {0}


Max(x, y) == IF x < y THEN y ELSE x

(* --algorithm manage_clock
variables
  Tick = 0,
  Counters = [p \in Processes |-> 0],
  Trace = {},
  msgtime;

define
  Perms == Permutations(Processes)

  RECURSIVE HappensBefore (_, _)
  HappensBefore (e1, e2) ==
   /\ e1.tick < e2.tick
   /\ e1.recv = e2.send
      \/ \E e \in Trace :
        /\ e1.tick < e.tick
        /\ e.tick < e2.tick
        /\ HappensBefore(e1, e)
        /\ HappensBefore(e, e2)

  Causal == \A e1 \in Trace : \A e2 \in Trace :
    HappensBefore(e1, e2) => e1.counter < e2.counter
end define;

begin
  while Tick < Steps do
    with send \in Processes, recv \in Processes \ {send} do
      \* print [tick |-> Tick, from |-> send, to |-> rcv];
      msgtime := Counters[send] + 1;
      Counters[send] := msgtime ||
      Counters[recv] := Max(msgtime, Counters[recv]) + 1;
      Trace := Trace \union {
        [send |-> send, recv |-> recv, tick |-> Tick, counter |-> msgtime]
      }
    end with;

    Tick := Tick + 1;
  end while;
end algorithm; *)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES Tick, Counters, Trace, msgtime, pc

(* define statement *)
Perms == Permutations(Processes)

RECURSIVE HappensBefore (_, _)
HappensBefore (e1, e2) ==
 /\ e1.tick < e2.tick
 /\ e1.recv = e2.send
    \/ \E e \in Trace :
      /\ e1.tick < e.tick
      /\ e.tick < e2.tick
      /\ HappensBefore(e1, e)
      /\ HappensBefore(e, e2)

Causal == \A e1 \in Trace : \A e2 \in Trace :
  HappensBefore(e1, e2) => e1.counter < e2.counter


vars == << Tick, Counters, Trace, msgtime, pc >>

Init == (* Global variables *)
        /\ Tick = 0
        /\ Counters = [p \in Processes |-> 0]
        /\ Trace = {}
        /\ msgtime = defaultInitValue
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF Tick < Steps
               THEN /\ \E send \in Processes:
                         \E recv \in Processes \ {send}:
                           /\ msgtime' = Counters[send] + 1
                           /\ Counters' = [Counters EXCEPT ![send] = msgtime',
                                                           ![recv] = Max(msgtime', Counters[recv]) + 1]
                           /\ Trace' = (         Trace \union {
                                          [send |-> send, recv |-> recv, tick |-> Tick, counter |-> msgtime']
                                        })
                    /\ Tick' = Tick + 1
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << Tick, Counters, Trace, msgtime >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
====
