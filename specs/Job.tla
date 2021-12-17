---- MODULE Job ----

vars == <<>>

ServerReceivesJob ==
  FALSE

RunnerRequestsJob ==
  FALSE

ServerAssignsJob ==
  FALSE

RunnerAcksJob ==
  FALSE

RunnerNacksJob ==
  FALSE

AckTimesOut ==
  FALSE

JobSucceeds ==
  FALSE

JobFails ==
  FALSE

JobExpires ==
  FALSE

Init ==
  TRUE

Next ==
  \/ ServerReceivesJob
  \/ RunnerRequestsJob
  \/ ServerAssignsJob
  \/ RunnerAcksJob
  \/ RunnerNacksJob
  \/ AckTimesOut
  \/ JobSucceeds
  \/ JobFails
  \/ JobExpires

Spec == Init /\ [][Next]_vars

====
