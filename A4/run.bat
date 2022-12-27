@echo off
copy .\tai-e\src\main\java\pascal\taie\analysis\dataflow\inter\InterConstantPropagation.java .
copy .\tai-e\src\main\java\pascal\taie\analysis\dataflow\inter\InterSolver.java .
copy .\tai-e\src\main\java\pascal\taie\analysis\graph\callgraph\CHABuilder.java .
zip foo.zip ./InterConstantPropagation.java ./InterSolver.java ./CHABuilder.java -x tai-e