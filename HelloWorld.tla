----------------------------- MODULE HelloWorld -----------------------------
EXTENDS Naturals

(*
--algorithm HelloWorld
variables n = 0;
begin
    n := n + 1;
end algorithm;
*)
\* BEGIN TRANSLATION
VARIABLES n, pc

vars == << n, pc >>

Init == (* Global variables *)
        /\ n = 0
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ n' = n + 1
         /\ pc' = "Done"

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

AlgoOK == pc = "Done" => n = 1

=============================================================================
\* Modification History
\* Last modified Thu Nov 30 22:04:10 PST 2017 by satya
\* Created Thu Nov 30 22:02:24 PST 2017 by satya
