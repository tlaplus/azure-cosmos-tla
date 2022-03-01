
  $ wget https://github.com/tlaplus/CommunityModules/releases/latest/download/CommunityModules-deps.jar
  $ java -jar tla2tools.jar -workers 1 -config scenario1.tla scenario1.tla

----------------------------- MODULE scenario1 -----------------------------
EXTENDS TLC, Integers, Sequences, IOUtils

AbsolutePathOfTLC == 
    TLCGet("config").install

Cmd ==
    <<"bash",
    "-c",
    "java " \o
    "-XX:+UseParallelGC " \o
    "-Dtlc2.value.Values.width=1000 " \o
    "-cp %1$s " \o
    "tlc2.TLC " \o
    "-checkpoint 0 -noTE -workers auto MCswscop.tla">>

-----------------------------------------------------------------------------

Consistency ==
    \* Evetual is equivalent to Consisten_Prefix
    <<"Eventual"(*, "Consistent_Prefix"*), "Session", "Bounded_Staleness", "Strong">>

ASSUME \A comb \in ((DOMAIN Consistency) \X (DOMAIN Consistency)) :
    LET conf == [mcConsistency |-> Consistency[comb[1]], mcProperty |-> Consistency[comb[2]]]
        ret == IOEnvExecTemplate(conf, Cmd, <<AbsolutePathOfTLC>>).exitValue
    IN CASE ret =  0 -> IF comb[1] >= comb[2] THEN TRUE ELSE Print(<<Consistency[comb[1]],Consistency[comb[2]],"No expected violation">>, TRUE)
         [] ret = 10 -> PrintT(<<conf, "Assumption violation">>)
         [] ret = 12 -> IF comb[1] < comb[2] THEN TRUE ELSE PrintT(<<conf, "Safety violation">>)
         [] ret = 13 -> PrintT(<<conf, "Liveness violation">>)
         [] OTHER    -> Print(<<conf, IOEnvExecTemplate(conf, Cmd, <<AbsolutePathOfTLC>>), "Error">>, FALSE)

=============================================================================
-------- CONFIG scenario1 --------
\* TLC always expects a config file
===================================