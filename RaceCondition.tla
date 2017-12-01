--------------------------- MODULE RaceCondition ---------------------------
EXTENDS Naturals
CONSTANT N

(*
--algorithm RaceCondition
variables total = 0;

process Proc \in 1..N
variable x
begin
 read:  x := total;
  inc:  x := x + 1;
 save:  total := x;
end process;

end algorithm;
*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES total, pc, x

vars == << total, pc, x >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ total = 0
        (* Process Proc *)
        /\ x = [self \in 1..N |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "read"]

read(self) == /\ pc[self] = "read"
              /\ x' = [x EXCEPT ![self] = total]
              /\ pc' = [pc EXCEPT ![self] = "inc"]
              /\ total' = total

inc(self) == /\ pc[self] = "inc"
             /\ x' = [x EXCEPT ![self] = x[self] + 1]
             /\ pc' = [pc EXCEPT ![self] = "save"]
             /\ total' = total

save(self) == /\ pc[self] = "save"
              /\ total' = x[self]
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ x' = x

Proc(self) == read(self) \/ inc(self) \/ save(self)

Next == (\E self \in 1..N: Proc(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

AlgoOK == (\A self \in ProcSet: pc[self] = "Done") => total = N

=============================================================================
\* Modification History
\* Last modified Thu Nov 30 18:40:12 PST 2017 by satya
\* Created Thu Nov 30 17:59:30 PST 2017 by satya
