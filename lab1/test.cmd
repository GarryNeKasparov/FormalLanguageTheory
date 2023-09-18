CALL > %2
CALL > %3
CALL rlc main.ref > nul & main.exe %1 %2 > nul
CALL yices-smt2 %2 > %3
CALL rlc BuildAnswer.ref > nul & BuildAnswer.exe %3
CALL del %2 %3 main.exe BuildAnswer.exe