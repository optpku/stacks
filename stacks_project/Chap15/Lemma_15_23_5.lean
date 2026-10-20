module

public import ReasLib.Algebra.Module.Reflexive
import StacksCheckRecall

/-!
# Lemma 15.23.5

This file recalls the exact-sequence closure property of finite reflexive modules.

@stack 0EB8
-/

@[expose] public section

open Module

universe u v w x

/- Lemma 15.23.5: in an exact sequence of finite modules over a Noetherian domain, a reflexive
middle term and torsion-free target force the source to be reflexive. -/
@[stacks 0EB8 "Lemma 15.23.5"]
#check @Module.IsReflexive.of_exact_of_torsionFree

/- The reusable form requiring only a finite middle term and a torsion-free represented quotient. -/
#check @Module.IsReflexive.of_exact_of_range_torsionFree
