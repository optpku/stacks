/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory

/-- An integer-valued function records the normalization degrees of a derived complex when,
at every prime, derived coextension to the residue field is the residue field in that degree. -/
def IsNormalizationDegreeFunction
    {A : Type u} [CommRing A]
    (ω : DerivedCategory (ModuleCat.{u} A))
    (δ : PrimeSpectrum A → ℤ) : Prop :=
  ∀ p : PrimeSpectrum A,
    Nonempty
      ((ModuleCat.derivedCoextensionOfScalars
          (algebraMap A p.asIdeal.ResidueField)).obj ω ≅
        (shiftFunctor
          (DerivedCategory (ModuleCat.{u} p.asIdeal.ResidueField)) (δ p)).obj
            (ModuleCat.single0
              (ModuleCat.of p.asIdeal.ResidueField p.asIdeal.ResidueField)))

/-- The pointwise residue-field characterization supplied by a normalization-degree function. -/
theorem IsNormalizationDegreeFunction.at
    {A : Type u} [CommRing A]
    {ω : DerivedCategory (ModuleCat.{u} A)}
    {δ : PrimeSpectrum A → ℤ}
    (hδ : IsNormalizationDegreeFunction ω δ)
    (p : PrimeSpectrum A) :
    Nonempty
      ((ModuleCat.derivedCoextensionOfScalars
          (algebraMap A p.asIdeal.ResidueField)).obj ω ≅
        (shiftFunctor
          (DerivedCategory (ModuleCat.{u} p.asIdeal.ResidueField)) (δ p)).obj
            (ModuleCat.single0
              (ModuleCat.of p.asIdeal.ResidueField p.asIdeal.ResidueField))) := sorry

end CategoryTheory.DerivedCategory

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/-- For a surjective map of Noetherian commutative rings, the normalization-degree function of
the derived coextension of a dualizing complex is pulled back along the spectrum map. -/
theorem normalizationDegreeFunction_coextensionOfSurjective
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} B))]
    (f : A →+* B) (hf : Function.Surjective f)
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HB : MonoidalClosed (DerivedCategory (ModuleCat.{u} B)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex HA)
    (δA : PrimeSpectrum A → ℤ) (δB : PrimeSpectrum B → ℤ)
    (hδA : IsNormalizationDegreeFunction ω δA)
    (hδB : IsNormalizationDegreeFunction
      ((ModuleCat.derivedCoextensionOfScalars f).obj ω) δB) :
    δB = δA ∘ _root_.PrimeSpectrum.comap f := sorry

end CategoryTheory.DerivedCategory.IsDualizingComplex
