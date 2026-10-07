module

public import ReasLib.RingTheory.Normal.Nagata.IntegralClosure
import StacksCheckRecall

@[expose] public section

/-!
# Finite Normalization in Reduced Essentially Finite-Type Nagata Algebras

@stack 03GH

The neutral finite-normalization statement is owned by ReasLib; this chapter
file preserves the textbook entry point.
-/

-- Lemma 10.162.2, tag `03GH`: if `R` is Nagata and `S` is reduced and
-- essentially of finite type over `R`, then `integralClosure R S` is finite
-- over `R`.
@[stacks 03GH]
#check @NagataRing.moduleFinite_integralClosure_of_essFiniteType_of_isReduced
