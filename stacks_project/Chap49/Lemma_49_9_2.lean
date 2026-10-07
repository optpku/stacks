module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.DedekindDifferent
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
import StacksCheckRecall

@[expose] public section

noncomputable section

open AlgebraicGeometry
open scoped Algebra.TensorProduct.Right TensorProduct

universe u

/- Lemma 49.9.2: on the affine presentation `Spec B → Spec A` of a flat
quasi-finite morphism of Noetherian schemes for which the Dedekind different is
defined, the different ideal sheaf is the ideal sheaf associated to the Dedekind
different of `A → B`. -/
@[stacks 0BW5] #check
  (Algebra.RelativeDualizingModule.differentIdealSheaf_eq_dedekindDifferent :
    ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
      [IsNoetherianRing A] [IsNoetherianRing B] [Module.Finite A B] [Module.Flat A B]
      (h_regular : ∀ a ∈ nonZeroDivisors A,
        algebraMap A B a ∈ nonZeroDivisors B)
      [Algebra.Etale (FractionRing A) (B ⊗[A] FractionRing A)],
      Scheme.idealSheafDataOfIdealOnSpec
          (Algebra.RelativeDualizingModule.differentIdeal A B) =
        Scheme.idealSheafDataOfIdealOnSpec
          (Algebra.RelativeDualizingModule.dedekindDifferentIdeal A B))
