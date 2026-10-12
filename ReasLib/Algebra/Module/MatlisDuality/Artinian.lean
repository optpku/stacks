/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Injective.Hull.Length
public import ReasLib.Algebra.Module.Reflexive.Relative

@[expose] public section

universe u v w

namespace Module

/-- Every finite module over an Artinian local ring is reflexive relative to an
injective module containing the residue field as an injective hull. -/
theorem isReflexiveRelativeTo_of_injectiveHull
    (R : Type u) (E : Type v) (M : Type w) [CommRing R] [IsLocalRing R]
    [IsArtinianRing R] [AddCommGroup E] [Module R E] [Module.Injective R E]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : ι.IsInjectiveHull) :
    Module.IsReflexiveRelativeTo R E M := sorry

/-- For an injective hull of the residue field over an Artinian local ring, scalar
action gives a bijection from the ring to the endomorphism ring. -/
theorem toModuleEnd_bijective_of_injectiveHull
    (R : Type u) (E : Type v) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    [AddCommGroup E] [Module R E] [Module.Injective R E]
    (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : ι.IsInjectiveHull) :
    Function.Bijective (Module.toModuleEnd R E : R →+* Module.End R E) := sorry

end Module
