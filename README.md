# final-project
Verifying Redis' intset.c implementation with Microsoft's Dafny

## frama-c
Folder containing frama-c implementation of verification of intsetAdd from intset.c
Since we were unable to get frama-c working, it is unknown if these conditions will work in frama-c

## redis_intset.dfy
Translation of methods from intset.c into Dafny language along with added verification conditions.