module

public import Mathlib.RingTheory.Smooth.IntegralClosure
public import ReasLib.RingTheory.RingHom.IndSmooth.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Integral closure under ind-smooth base change

The comparison map supplied by Mathlib for smooth base change remains bijective when the
base-change algebra is only ind-smooth.  This is the reusable source-level bridge; the
filtered-colimit presentation and its finite-data descent are proof infrastructure rather
than part of the public API.

@stack 0CBF
-/

@[expose] public section

open scoped TensorProduct

namespace TensorProduct

universe u v w

variable {R : Type u} {S : Type v} {B : Type w}
  [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B]

/-- Lemma 10.147.5: the canonical map from `S ⊗[R] integralClosure R B` to
`integralClosure S (S ⊗[R] B)` is bijective when `R → S` is ind-smooth. -/
@[stacks 0CBF]
theorem toIntegralClosure_bijective_of_indSmooth
    (hS : (algebraMap R S).IndSmooth) :
    Function.Bijective (toIntegralClosure R S B) := sorry

end TensorProduct
