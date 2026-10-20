/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.ComparisonEulerCharacteristic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.PuncturedSpectrum
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.CoherentTriple

/-- An integer is an Euler value when it is the section-length defect of a coherent
extension whose multiplication by the defining element is injective and whose closed-fiber
map is compatible with the canonical pullback–restriction isomorphism. -/
def IsEulerValue (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A) :
    let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
    let U₀ := S.y ⁻¹ᵁ S.U
    ∀ (F : S.U.toScheme.Modules) (F₀ : S.Y.Modules) [F.IsCoherent] [F₀.IsCoherent],
      (∀ V : S.U.toScheme.Opens, Function.Injective
        (F.smul (S.U.toScheme.presheaf.map V.leTop.op (S.U.ι.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))).hom) →
      (α : (pullback (S.y ∣_ S.U)).obj F ≅ F₀.restrict U₀.ι) →
      ℤ → Prop := by
  let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
    (IsLocalRing.maximalIdeal A)
    ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
  let U₀ := S.y ⁻¹ᵁ S.U
  exact fun F F₀ _ _ hF α z =>
    ∃ F' : S.X.Modules, F'.IsCoherent ∧
      (∀ V : S.X.Opens, Function.Injective
        (F'.smul (S.X.presheaf.map V.leTop.op
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f))).hom) ∧
      ∃ (α' : F'.restrict S.U.ι ≅ F) (β : (pullback S.y).obj F' ⟶ F₀),
        (pullback (S.y ∣_ S.U)).map α'.hom ≫ α.hom =
            (pullbackRestrictIso S.y S.U F').hom ≫
              (restrictFunctor U₀.ι).map β ∧
          z = sectionLengthDefect S.y β

/-- The intrinsic Euler characteristic is the chosen integer represented by an admissible
comparison, with value zero only when no such integer is represented. -/
noncomputable def eulerCharacteristic (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A) :
    let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
    let U₀ := S.y ⁻¹ᵁ S.U
    ∀ (F : S.U.toScheme.Modules) (F₀ : S.Y.Modules) [F.IsCoherent] [F₀.IsCoherent],
      (hF : ∀ V : S.U.toScheme.Opens, Function.Injective
        (F.smul (S.U.toScheme.presheaf.map V.leTop.op (S.U.ι.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))).hom) →
      (α : (pullback (S.y ∣_ S.U)).obj F ≅ F₀.restrict U₀.ι) → ℤ :=
  fun F F₀ _ _ hF α => by
    classical
    exact if h : ∃ z, IsEulerValue A f hf_mem F F₀ hF α z then Classical.choose h else 0

/-- Under regularity, the intrinsic Euler characteristic is represented by an admissible
coherent extension and its canonical closed-fiber compatibility map. -/
theorem eulerCharacteristic_spec (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hf_regular : IsRegular f) :
    let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
    let U₀ := S.y ⁻¹ᵁ S.U
    ∀ (F : S.U.toScheme.Modules) (F₀ : S.Y.Modules) [F.IsCoherent] [F₀.IsCoherent],
      (hF : ∀ V : S.U.toScheme.Opens, Function.Injective
        (F.smul (S.U.toScheme.presheaf.map V.leTop.op (S.U.ι.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))).hom) →
      (α : (pullback (S.y ∣_ S.U)).obj F ≅ F₀.restrict U₀.ι) →
      IsEulerValue A f hf_mem F F₀ hF α
        (eulerCharacteristic A f hf_mem F F₀ hF α) := sorry

/-- Every admissible coherent comparison computes the intrinsic Euler characteristic through
the canonical pullback–restriction compatibility square. -/
theorem eulerCharacteristic_eq_comparison (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hf_regular : IsRegular f) :
    let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
    let U₀ := S.y ⁻¹ᵁ S.U
    ∀ (F : S.U.toScheme.Modules) (F₀ : S.Y.Modules) [F.IsCoherent] [F₀.IsCoherent],
      (hF : ∀ V : S.U.toScheme.Opens, Function.Injective
        (F.smul (S.U.toScheme.presheaf.map V.leTop.op (S.U.ι.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))).hom) →
      (α : (pullback (S.y ∣_ S.U)).obj F ≅ F₀.restrict U₀.ι) →
      ∀ (F' : S.X.Modules), F'.IsCoherent →
        (∀ V : S.X.Opens, Function.Injective
          (F'.smul (S.X.presheaf.map V.leTop.op
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f))).hom) →
        ∀ (α' : F'.restrict S.U.ι ≅ F) (β : (pullback S.y).obj F' ⟶ F₀),
          (pullback (S.y ∣_ S.U)).map α'.hom ≫ α.hom =
            (pullbackRestrictIso S.y S.U F').hom ≫
              (restrictFunctor U₀.ι).map β →
          eulerCharacteristic A f hf_mem F F₀ hF α = sectionLengthDefect S.y β := sorry

/-- The intrinsic Euler characteristic is additive for componentwise short exact sequences
whose punctured and closed-fiber maps commute with the three fixed identifications. -/
theorem eulerCharacteristic_eq_add_of_shortExact (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (f : A)
    (hf_mem : f ∈ IsLocalRing.maximalIdeal A) (hf_regular : IsRegular f) :
    let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
    let U₀ := S.y ⁻¹ᵁ S.U
    ∀ (E : CategoryTheory.ShortComplex S.U.toScheme.Modules)
      (E₀ : CategoryTheory.ShortComplex S.Y.Modules)
      [E.X₁.IsCoherent] [E.X₂.IsCoherent] [E.X₃.IsCoherent]
      [E₀.X₁.IsCoherent] [E₀.X₂.IsCoherent] [E₀.X₃.IsCoherent],
        (h₁ : ∀ V : S.U.toScheme.Opens, Function.Injective
          (E.X₁.smul (S.U.toScheme.presheaf.map V.leTop.op (S.U.ι.appTop
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))).hom) →
        (h₂ : ∀ V : S.U.toScheme.Opens, Function.Injective
          (E.X₂.smul (S.U.toScheme.presheaf.map V.leTop.op (S.U.ι.appTop
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))).hom) →
        (h₃ : ∀ V : S.U.toScheme.Opens, Function.Injective
          (E.X₃.smul (S.U.toScheme.presheaf.map V.leTop.op (S.U.ι.appTop
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)))).hom) →
      (α₁ : (pullback (S.y ∣_ S.U)).obj E.X₁ ≅ E₀.X₁.restrict U₀.ι) →
      (α₂ : (pullback (S.y ∣_ S.U)).obj E.X₂ ≅ E₀.X₂.restrict U₀.ι) →
      (α₃ : (pullback (S.y ∣_ S.U)).obj E.X₃ ≅ E₀.X₃.restrict U₀.ι) →
      (pullback (S.y ∣_ S.U)).map E.f ≫ α₂.hom =
          α₁.hom ≫ (restrictFunctor U₀.ι).map E₀.f →
      (pullback (S.y ∣_ S.U)).map E.g ≫ α₃.hom =
          α₂.hom ≫ (restrictFunctor U₀.ι).map E₀.g →
      E.ShortExact → E₀.ShortExact →
      eulerCharacteristic A f hf_mem E.X₂ E₀.X₂ h₂ α₂ =
        eulerCharacteristic A f hf_mem E.X₁ E₀.X₁ h₁ α₁ +
          eulerCharacteristic A f hf_mem E.X₃ E₀.X₃ h₃ α₃ := sorry

end AlgebraicGeometry.Scheme.Modules.CoherentTriple
