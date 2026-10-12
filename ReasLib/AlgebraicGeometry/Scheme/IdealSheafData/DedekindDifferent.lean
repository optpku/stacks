/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import ReasLib.RingTheory.DedekindDifferent.Ideal

@[expose] public section

noncomputable section

open AlgebraicGeometry
open scoped Algebra.TensorProduct.Right TensorProduct

universe u

namespace Algebra.RelativeDualizingModule

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [h_noetherian : IsNoetherianRing A] [h_noetherian_B : IsNoetherianRing B]
variable [h_finite : Module.Finite A B] [h_flat : Module.Flat A B]
variable (h_regular : ∀ a ∈ nonZeroDivisors A,
  algebraMap A B a ∈ nonZeroDivisors B)
variable [h_etale : Algebra.Etale (FractionRing A) (B ⊗[A] FractionRing A)]

include h_noetherian h_noetherian_B h_finite h_flat h_regular h_etale

/-- For a finite flat Noetherian algebra with etale generic fibre, the
relative-dualizing-module different ideal and the Dedekind different ideal
define the same ideal sheaf datum on the affine spectrum. -/
theorem differentIdealSheaf_eq_dedekindDifferent :
    Scheme.idealSheafDataOfIdealOnSpec (differentIdeal A B) =
      Scheme.idealSheafDataOfIdealOnSpec (dedekindDifferentIdeal A B) := sorry

end Algebra.RelativeDualizingModule
