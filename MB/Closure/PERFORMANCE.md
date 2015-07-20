Choosing a data representation
------------------------------

test case compile and run

```
ghc -O2 -funbox-strict-fields closuretest.hs -rtsopts 
time ./closuretest +RTS -M1G -RTS ~/tpdb/tpdb-4.0/SRS/Gebhardt/06.srs -b
```

Results
```
Data.ByteString      :  6.0 s
Data.ByteString.Lazy : 10.7 s
Data.Text            :  8.8 s
Data.Text.Lazy       : 17.7 s
Data.List	     : 10.6 s
```
result: Data.ByteString looks best.

Micro-Optimisations
-------------------

Profiling: compile
```
ghc -O2 -funbox-strict-fields closuretest.hs -rtsopts -prof -auto-all
```
Results (for RTS args)
```
(empty)  : 11 s
-p -h    : 55 s
```
This  takes too long, I am using a different test case
```
time ./closuretest +RTS -M1G -RTS ~/tpdb/tpdb-4.0/SRS/Gebhardt/06.srs  +RTS -p -h
```
Results
```
(empty)  : 1.2 s
-p -h    : 1.4 s
```
top cost centers:
```
COST CENTRE   MODULE               %time %alloc

insides       MB.Closure.Data       31.4   13.4
work_fc.go    MB.Closure.Enumerate  22.2   28.8
rights        MB.Closure.Data       16.6   17.6
looping       MB.Closure.Enumerate   5.8   17.3
compare       MB.Closure.Data        5.1    0.0
```
in `insides` we are really matching lhss of rules,
in `work_fc` we are managing the priority queue.

Cost of rule matching
---------------------

replace split-and-test by
```
Data.ByteString.Search (indices)      :  0.83 s
Data.ByteString.Search.DFA (indices)  :  0.92 s
Data.ByteString.Search.KMP (indices)  :  0.73 s
```
Result: use KMP. Detailed cost
(note: insides is now below rights)
```
COST CENTRE   MODULE               %time %alloc

work_fc.go    MB.Closure.Enumerate  32.4   27.2
rights        MB.Closure.Data       18.6   16.7
insides       MB.Closure.Data       13.1   16.8
looping       MB.Closure.Enumerate   8.1   16.4
compare       MB.Closure.Data        5.2    0.0
```

Cost for Priority Queue implementation
--------------------------------------

with Data.PQueue.Min (the priority is based on the
Ord instance of the closures)
```
foldr' Q.insert xs    : 0.72 s
foldr  Q.insert xs    : 0.66 s
```
with Data.PQueue.Prio.Min (priority just by size):
```
foldr' : 0.60

work_fc.go   MB.Closure.Enumerate  22.5   23.7
rights       MB.Closure.Data       21.4   16.5
insides      MB.Closure.Data       19.7   16.8
looping      MB.Closure.Enumerate  10.6   16.3

foldr : 0.58

rights       MB.Closure.Data       26.3   16.8
insides      MB.Closure.Data       19.9   17.1
work_fc.go   MB.Closure.Enumerate  18.5   20.5
looping      MB.Closure.Enumerate   9.2   16.6
```
now run original test case again (without profiling): 4.3 s.
Nice, down 25 percent (from 6 s).

