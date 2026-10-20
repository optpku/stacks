module

public import ReasLib.Algebra.Module.Reflexive.Normal
import StacksCheckRecall

/-!
# Lemma 15.23.20

@stack 0BM4

Finite integral closures in finite fraction-field extensions use the canonical reflexive-module
instance from ReasLib.
-/

@[expose] public section

/- Lemma 15.23.20: if `A` is a Noetherian normal domain and `L / FractionRing A` is finite, then
the finite `A`-module `integralClosure A L` is reflexive. -/
@[stacks 0BM4 "Lemma 15.23.20"]
#check @integralClosure.instIsReflexiveOfFinite
