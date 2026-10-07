module

public import ReasLib.Algebra.Module.IdealDuality
public import ReasLib.Algebra.Module.MatlisDuality.FinitelyGenerated

@[expose] public section

universe u v w

namespace LinearMap.IsInjectiveHull

/-- Restriction identifies the dual of the ideal-annihilated part of a finite module with
the quotient of its dual by the ideal, under finite Matlis duality hypotheses. -/
theorem quotientDualToDualTorsion_bijective
    (R : Type u) (E : Type v) (M : Type w) [CommRing R] [IsLocalRing R]
    [IsArtinianRing R] [AddCommGroup E] [Module R E] [Module.Injective R E]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    {ι : IsLocalRing.ResidueField R →ₗ[R] E} (hι : ι.IsInjectiveHull) (I : Ideal R) :
    Function.Bijective (Module.IdealDuality.quotientDualToDualTorsion R E I M) := sorry

/-- Precomposition identifies the dual of an ideal quotient with the ideal-annihilated
part of the dual of a finite module, under finite Matlis duality hypotheses. -/
theorem dualQuotientToTorsion_bijective
    (R : Type u) (E : Type v) (M : Type w) [CommRing R] [IsLocalRing R]
    [IsArtinianRing R] [AddCommGroup E] [Module R E] [Module.Injective R E]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    {ι : IsLocalRing.ResidueField R →ₗ[R] E} (hι : ι.IsInjectiveHull) (I : Ideal R) :
    Function.Bijective (Module.IdealDuality.dualQuotientToTorsion R E I M) := sorry

end LinearMap.IsInjectiveHull
