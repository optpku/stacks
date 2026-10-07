module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.FiniteLocallyFreeStage
public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization
public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Open
public import ReasLib.RingTheory.Depth.NormalLocal
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Intrinsic.Existence

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- Over a complete Noetherian normal local ring of dimension at least four, a coherent
formal module with finite locally free stages on the principal formal completion of
the punctured spectrum along a nonzero maximal-ideal element admits a coherent algebraization. -/
theorem isCompletion_of_normal_local_dim_ge_four
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsCompleteLocalRing A] [IsNormalRing A]
    [Fact (4 ≤ ringKrullDim A)]
    (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (f : A)
    (h_a : S.a = IsLocalRing.maximalIdeal A)
    (h_I : S.I = Ideal.span ({f} : Set A))
    (h_f_mem : f ∈ IsLocalRing.maximalIdeal A)
    (h_f_ne : f ≠ 0)
    (h_stageFree : ∀ n : ℕ, IsFiniteLocallyFreeStage F n) :
    (CoherentCompletion.functor
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).essImage F := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
