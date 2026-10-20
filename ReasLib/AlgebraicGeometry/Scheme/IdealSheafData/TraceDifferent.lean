module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import ReasLib.RingTheory.DedekindDifferent.TraceDifferent

@[expose] public section

open AlgebraicGeometry
open scoped Algebra.DualModule Algebra.TensorProduct.Right TensorProduct

noncomputable section

universe u

namespace Algebra.RelativeDualizingModule

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [h_noetherian : IsNoetherianRing A] [h_finite : Module.Finite A B]
variable
  (h_regular : ∀ a ∈ nonZeroDivisors A,
    algebraMap A B a ∈ nonZeroDivisors B)
variable
  [h_etale : Algebra.Etale (FractionRing A) (B ⊗[A] FractionRing A)]

include h_noetherian h_finite h_regular h_etale

/-- The affine ideal-sheaf datum of the generalized trace different agrees with
the ideal-sheaf datum associated to the ideal-valued Dedekind different. -/
theorem traceDifferentIdealSheaf_eq_dedekindDifferent
    (h_one : (1 : B ⊗[A] FractionRing A) ∈
      Submodule.dedekindComplementary A (FractionRing A) B
        (B ⊗[A] FractionRing A)) :
    Scheme.idealSheafDataOfIdealOnSpec
        (Module.annihilator B
          (Module.Dual A B ⧸ Submodule.span B
            {dedekindComparison A B ⟨1, h_one⟩})) =
      Scheme.idealSheafDataOfIdealOnSpec
        (dedekindDifferentIdeal A B) := sorry

end Algebra.RelativeDualizingModule
