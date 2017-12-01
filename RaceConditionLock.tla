------------------------- MODULE RaceConditionLock -------------------------
EXTENDS Naturals
CONSTANT N

(*
--algorithm RaceConditionLock
variables total = 0, have_lock = FALSE;

macro Lock()
begin
    await have_lock = FALSE;
    have_lock := TRUE;
end macro;

macro Unlock()
begin
    have_lock := FALSE;
end macro;

process Proc \in 1..N
variable x
begin
  lock: Lock();
  read: x := total;
   inc: x := x + 1;
  save: total := x;
unlock: Unlock();
end process;

end algorithm;
*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES total, have_lock, pc, x

vars == << total, have_lock, pc, x >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ total = 0
        /\ have_lock = FALSE
        (* Process Proc *)
        /\ x = [self \in 1..N |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "lock"]

lock(self) == /\ pc[self] = "lock"
              /\ have_lock = FALSE
              /\ have_lock' = TRUE
              /\ pc' = [pc EXCEPT ![self] = "read"]
              /\ UNCHANGED << total, x >>

read(self) == /\ pc[self] = "read"
              /\ x' = [x EXCEPT ![self] = total]
              /\ pc' = [pc EXCEPT ![self] = "inc"]
              /\ UNCHANGED << total, have_lock >>

inc(self) == /\ pc[self] = "inc"
             /\ x' = [x EXCEPT ![self] = x[self] + 1]
             /\ pc' = [pc EXCEPT ![self] = "save"]
             /\ UNCHANGED << total, have_lock >>

save(self) == /\ pc[self] = "save"
              /\ total' = x[self]
              /\ pc' = [pc EXCEPT ![self] = "unlock"]
              /\ UNCHANGED << have_lock, x >>

unlock(self) == /\ pc[self] = "unlock"
                /\ have_lock' = FALSE
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << total, x >>

Proc(self) == lock(self) \/ read(self) \/ inc(self) \/ save(self)
                 \/ unlock(self)

Next == (\E self \in 1..N: Proc(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

AlgoOK == (\A self \in ProcSet: pc[self] = "Done") => total = N

=============================================================================
\* Modification History
\* Last modified Fri Dec 01 12:10:52 PST 2017 by satya
\* Created Thu Nov 30 18:44:41 PST 2017 by satya
