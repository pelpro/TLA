---- MODULE deadlock ----
EXTENDS TLC, Integers, FiniteSets
VARIABLES MutexState, CriticalSection, next0, next1

Init == /\ MutexState = [t \in {1,2} |-> FALSE] 
        /\ CriticalSection = [t \in {1,2} |-> FALSE] 
        /\ next0 = 0
        /\ next1 = 0
MonitorEnter(t) == /\ MutexState[t] = FALSE
                   /\ MutexState' = [MutexState EXCEPT ![t] = TRUE]
                   /\ UNCHANGED CriticalSection

MonitorExit(t) == /\ MutexState[t] = TRUE
                  /\ MutexState' = [MutexState EXCEPT ![t] = FALSE]
                  /\ UNCHANGED CriticalSection

EnterCriticalSection(t) == /\ CriticalSection' = [CriticalSection EXCEPT ![t] = TRUE]
                           /\ UNCHANGED MutexState

T0_0 == /\ next0 = 0
        /\ MonitorEnter(1)
        /\ next0' = next0 + 1 
        /\ UNCHANGED next1

T0_1 == /\ next0 = 1
        /\ MonitorEnter(2)
        /\ next0' = next0 + 1 
        /\ UNCHANGED next1

T0_2 == /\ next0 = 2
        /\ EnterCriticalSection(1)
        /\ next0' = next0 + 1 
        /\ UNCHANGED next1

T0_3 == /\ next0 = 3
        /\ MonitorExit(1)
        /\ next0' = next0 + 1 
        /\ UNCHANGED next1

T0_4 == /\ next0 = 4
        /\ MonitorExit(2)
        /\ next0' = next0 + 1 
        /\ UNCHANGED next1

T1_0 == /\ next1 = 0
        /\ MonitorEnter(2)
        /\ next1' = next1 + 1 
        /\ UNCHANGED next0

T1_1 == /\ next1 = 1
        /\ MonitorEnter(1)
        /\ next1' = next1 + 1 
        /\ UNCHANGED next0

T1_2 == /\ next1 = 2
        /\ EnterCriticalSection(2)
        /\ next1' = next1 + 1 
        /\ UNCHANGED next0

T1_3 == /\ next1 = 3
        /\ MonitorExit(2)
        /\ next1' = next1 + 1 
        /\ UNCHANGED next0
        
T1_4 == /\ next1 = 4
        /\ MonitorExit(1)
        /\ next1' = next1 + 1
        /\ UNCHANGED next0

Thread1 == T0_0 \/ T0_1 \/ T0_2 \/ T0_3 \/ T0_4

Thread2 == T1_0 \/ T1_1 \/ T1_2 \/ T1_3 \/ T1_4

Invariant == ~(CriticalSection[1] /\ CriticalSection[2])

Next == Thread1 \/ Thread2

============================================================================================================
