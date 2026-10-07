module

import StacksCheckRecall
import Mathlib.RingTheory.Flat.Basic
public import ReasLib.Algebra.Module.ContentIdeal.Finite

/-!
# Lemma 15.24.2

Finite generation is recalled from the generic least-content-ideal theorem.

@stack 0ASB
-/

@[expose] public section

universe u v

/- Lemma 15.24.2: the content ideal of an element of a flat module is finitely
generated. -/
@[stacks 0ASB "Lemma 15.24.2"]
#check fun (A : Type u) (M : Type v) [CommRing A] [AddCommGroup M]
    [Module A M] [Module.Flat A M] {x : M} {I : Ideal A}
    (hI : IsContentIdeal x I) ↦
  hI.fg

/- Finite generation only uses the least-ideal property. -/
#check @IsContentIdeal.fg
