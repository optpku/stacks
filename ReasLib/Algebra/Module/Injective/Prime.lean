module

public import ReasLib.Algebra.Module.Injective.Hull
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

@[expose] public section

universe u v

namespace LinearMap.IsInjectiveHull

/-- An injective hull of a prime quotient module is an indecomposable module. -/
theorem indecomposable_of_quotient
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {E : Type v} [AddCommGroup E] [Module R E] [Module.Injective R E]
    (i : R ⧸ p →ₗ[R] E) (hi : i.IsInjectiveHull) :
    CategoryTheory.Indecomposable (ModuleCat.of R E) := sorry

/-- An injective hull of a prime quotient extends to an injective hull of the
corresponding ideal residue field. -/
theorem exists_residueField
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {E : Type v} [AddCommGroup E] [Module R E] [Module.Injective R E]
    (i : R ⧸ p →ₗ[R] E) (hi : i.IsInjectiveHull) :
    ∃ j : p.ResidueField →ₗ[R] E,
      j.comp ((Algebra.linearMap (R ⧸ p) p.ResidueField).restrictScalars R) = i ∧
        j.IsInjectiveHull := sorry

/-- After localization at a prime, an injective hull of the prime quotient is
an injective hull of the residue field over the localized ring. -/
theorem exists_residueField_atPrime
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {E : Type v} [AddCommGroup E] [Module R E] [Module.Injective R E]
    (i : R ⧸ p →ₗ[R] E) (hi : i.IsInjectiveHull) :
    ∃ (e : E ≃ₗ[R] LocalizedModule.AtPrime p E)
        (hL : Module.Injective (Localization.AtPrime p) (LocalizedModule.AtPrime p E))
        (j : p.ResidueField →ₗ[Localization.AtPrime p] LocalizedModule.AtPrime p E),
      e.toLinearMap = LocalizedModule.mkLinearMap p.primeCompl E ∧
        (j.restrictScalars R).comp
            ((Algebra.linearMap (R ⧸ p) p.ResidueField).restrictScalars R) =
          (LocalizedModule.mkLinearMap p.primeCompl E).comp i ∧
        @LinearMap.IsInjectiveHull (Localization.AtPrime p) _ p.ResidueField _ _
          (LocalizedModule.AtPrime p E) _ _ hL j := sorry

end LinearMap.IsInjectiveHull
