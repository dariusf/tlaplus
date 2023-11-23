---------------------------- MODULE Common --------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC, TLCExt, Json

ToSet(s) == { s[i] : i \in DOMAIN s }
Option(T) == Seq(T)
Some(e) == <<e>>
None == <<>>

MapThenFoldSet(op(_,_), base, f(_), choose(_), S) ==
  LET iter[s \in SUBSET S] ==
        IF s = {} THEN base
        ELSE LET x == choose(s)
             IN  op(f(x), iter[s \ {x}])
  IN  iter[S]


FoldFunction(op(_,_), base, fun) ==
  MapThenFoldSet(op, base, LAMBDA i : fun[i], LAMBDA s: CHOOSE x \in s : TRUE, DOMAIN fun)

FoldSeq(op(_, _), base, seq) == 
  FoldFunction(op, base, seq)

Remove(s, e) ==
    SelectSeq(s, LAMBDA t: t # e)

RemoveAt(s, i) == 
  SubSeq(s, 1, i-1) \o SubSeq(s, i+1, Len(s))

IsPrefix(s, t) ==
  Len(s) <= Len(t) /\ SubSeq(s, 1, Len(s)) = SubSeq(t, 1, Len(s))

IsInjective(f) == \A a,b \in DOMAIN f : f[a] = f[b] => a = b

SetToSeq(S) == 
  CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)

=============================================================================