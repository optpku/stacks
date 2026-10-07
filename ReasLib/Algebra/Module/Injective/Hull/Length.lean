module

public import ReasLib.Algebra.Module.Injective.Hull
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

@[expose] public section

universe u v w

/-- Dualization into an injective hull of the residue field preserves the length of a
finite module over an Artinian local ring. -/
theorem Module.length_linearMap_to_injectiveHull
    (R : Type u) (E : Type v) (M : Type w) [CommRing R] [IsLocalRing R]
    [IsArtinianRing R] [AddCommGroup E] [Module R E] [Module.Injective R E]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : ι.IsInjectiveHull) :
    Module.length R M = Module.length R (M →ₗ[R] E) := sorry

/-- An injective hull of the residue field of an Artinian local ring is finite as a
module. -/
theorem Module.Finite.of_injectiveHull
    (R : Type u) (E : Type v) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    [AddCommGroup E] [Module R E] [Module.Injective R E]
    (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : ι.IsInjectiveHull) :
    Module.Finite R E := sorry
