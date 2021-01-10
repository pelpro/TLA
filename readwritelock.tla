---- MODULE readwritelock ----
EXTENDS TLC, Integers, FiniteSets
CONSTANTS Threads
ASSUME Cardinality(Threads) >= 1
VARIABLES CurrentReadersCount, CurrentWritersCount, ThreadState

TypeOK == /\ ThreadState \in [Threads -> {"Reading","Writing","Waiting","Finished"}]
         /\ CurrentReadersCount >= 0
         /\ CurrentWritersCount >= 0 /\ CurrentWritersCount <= 1

Init == ThreadState = [t \in Threads |-> "Waiting"] /\ CurrentReadersCount = 0 /\ CurrentWritersCount = 0

ReaderLocking(t) == \/ /\ CurrentWritersCount = 0 /\ ~(ThreadState[t] \in {"Finished"})
                       /\ ThreadState' = [ThreadState EXCEPT ![t] = "Reading"]
                       /\ CurrentReadersCount' = CurrentReadersCount + 1
                       /\ UNCHANGED CurrentWritersCount
                       /\ TypeOK

ReaderUnlocking(t) == /\ CurrentReadersCount > 0 /\ ThreadState[t] \in {"Reading"}
                      /\ CurrentReadersCount' = CurrentReadersCount - 1 
                      /\ ThreadState' = [ThreadState EXCEPT ![t] = "Finished"]
                      /\ UNCHANGED CurrentWritersCount
                      /\ TypeOK

WriterLocking(t) == \/ /\ CurrentReadersCount = 0 /\ ~(ThreadState[t] \in {"Finished"}) 
                       /\ CurrentWritersCount = 0
                       /\ ThreadState' = [ThreadState EXCEPT ![t] = "Writing"]
                       /\ CurrentWritersCount' = CurrentWritersCount + 1
                       /\ UNCHANGED CurrentReadersCount
                       /\ TypeOK

WriterUnlocking(t) == /\ CurrentWritersCount = 1 /\ ThreadState[t] \in {"Writing"}
                      /\ CurrentWritersCount' = CurrentWritersCount - 1 
                      /\ ThreadState' = [ThreadState EXCEPT ![t] = "Finished"]
                      /\ UNCHANGED CurrentReadersCount
                      /\ TypeOK

Next == \E t \in Threads: ReaderLocking(t) \/ ReaderUnlocking(t) \/ WriterLocking(t) \/ WriterUnlocking(t)
    
Spec == Init /\ [][Next]_<<CurrentReadersCount,CurrentWritersCount,ThreadState>> 
        
NoDoubleLock == \A t1 \in Threads: \A t2 \in (Threads \ {t1}): ~(/\ ThreadState[t1] \in {"Writing"}
                                                              /\ ThreadState[t2] \in {"Reading"})

============================================================================================================
