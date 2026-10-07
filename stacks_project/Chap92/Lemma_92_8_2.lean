module

public import stacks_project.Chap92.Lemma_92_8_1
import Mathlib.Tactic.CrossRefAttribute

/-!
# Vanishing of the cotangent complex along a derived diagonal

If `A → B` is a ring map with `B = B ⊗[A]^L B` in `D(B)`, then `L_{B/A}`
vanishes in `D(B)`.
-/

@[expose] public section

open Algebra.CotangentComplex
open CategoryTheory
open CategoryTheory.Limits
open RingedSite.Cotangent.Functoriality

universe u

namespace Algebra.CotangentComplex

/-- Lemma 92.8.2. Let `A → B` be a ring map such that `B = B ⊗[A]^L B`.
Then `L_{B/A} = 0` in `D(B)`, as vanishing of `derived A B`. -/
@[stacks 08R0]
theorem isZero_derived_of_derivedTensor (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (h : InducesDerivedTensorQuasiIso (idCodomainCommSq A B B)) :
    IsZero (derived A B) :=
  sorry

/-- Under the derived-tensor identity `B = B ⊗[A]^L B`, every homology module of
`Algebra.cotangentComplex A B` vanishes. -/
theorem isZero_homology_of_derivedTensor (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (h : InducesDerivedTensorQuasiIso (idCodomainCommSq A B B)) {n : ℤ} :
    IsZero ((Algebra.cotangentComplex A B).homology n) :=
  sorry

end Algebra.CotangentComplex
