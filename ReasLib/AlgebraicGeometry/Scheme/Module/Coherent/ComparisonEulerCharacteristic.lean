module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections.Length
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import Mathlib.Algebra.Regular.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- An admissible coherent comparison on a punctured local spectrum has length defect
equal to the closed-fiber cokernel length minus the closed-fiber kernel length over the
local ring. -/
theorem comparisonEulerCharacteristic_eq (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hf_regular : IsRegular f) :
    let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
    let U₀ := S.y ⁻¹ᵁ S.U
    let sX := (Scheme.ΓSpecIso (CommRingCat.of A)).inv f
    let sU := S.U.ι.appTop sX
    ∀ (F : S.U.toScheme.Modules) (F₀ : S.Y.Modules) [F.IsCoherent] [F₀.IsCoherent],
      (∀ V : S.U.toScheme.Opens, Function.Injective
        (F.smul (S.U.toScheme.presheaf.map V.leTop.op sU)).hom) →
      ∀ (α : (pullback (S.y ∣_ S.U)).obj F ≅ F₀.restrict U₀.ι)
        (F' : S.X.Modules) [F'.IsCoherent],
        (∀ V : S.X.Opens,
          Function.Injective (F'.smul (S.X.presheaf.map V.leTop.op sX)).hom) →
        ∀ (α' : F'.restrict S.U.ι ≅ F) (α₀' : (pullback S.y).obj F' ⟶ F₀),
          (pullback (S.y ∣_ S.U)).map α'.hom ≫ α.hom =
            (pullbackRestrictIso S.y S.U F').hom ≫
              (restrictFunctor U₀.ι).map α₀' →
          let linearMap := (S.y.globalSectionsFunctor.map α₀').hom
          sectionLengthDefect S.y α₀' =
            ((Module.length A (S.y.globalSectionsMod F₀ ⧸ linearMap.range)).toNat : ℤ) -
              ((Module.length A linearMap.ker).toNat : ℤ) := sorry

/-- The global-section kernel of an admissible closed-fiber coherent comparison on a
punctured local spectrum has finite length over the local ring. -/
theorem comparisonKernel_finiteLength (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hf_regular : IsRegular f) :
    let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
    let U₀ := S.y ⁻¹ᵁ S.U
    let sX := (Scheme.ΓSpecIso (CommRingCat.of A)).inv f
    let sU := S.U.ι.appTop sX
    ∀ (F : S.U.toScheme.Modules) (F₀ : S.Y.Modules) [F.IsCoherent] [F₀.IsCoherent],
      (∀ V : S.U.toScheme.Opens, Function.Injective
        (F.smul (S.U.toScheme.presheaf.map V.leTop.op sU)).hom) →
      ∀ (α : (pullback (S.y ∣_ S.U)).obj F ≅ F₀.restrict U₀.ι)
        (F' : S.X.Modules) [F'.IsCoherent],
        (∀ V : S.X.Opens,
          Function.Injective (F'.smul (S.X.presheaf.map V.leTop.op sX)).hom) →
        ∀ (α' : F'.restrict S.U.ι ≅ F) (α₀' : (pullback S.y).obj F' ⟶ F₀),
          (pullback (S.y ∣_ S.U)).map α'.hom ≫ α.hom =
            (pullbackRestrictIso S.y S.U F').hom ≫
              (restrictFunctor U₀.ι).map α₀' →
          IsFiniteLength A (S.y.globalSectionsFunctor.map α₀').hom.ker := sorry

/-- The global-section cokernel of an admissible closed-fiber coherent comparison on
a punctured local spectrum has finite length over the local ring. -/
theorem comparisonCokernel_finiteLength (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hf_regular : IsRegular f) :
    let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
    let U₀ := S.y ⁻¹ᵁ S.U
    let sX := (Scheme.ΓSpecIso (CommRingCat.of A)).inv f
    let sU := S.U.ι.appTop sX
    ∀ (F : S.U.toScheme.Modules) (F₀ : S.Y.Modules) [F.IsCoherent] [F₀.IsCoherent],
      (∀ V : S.U.toScheme.Opens, Function.Injective
        (F.smul (S.U.toScheme.presheaf.map V.leTop.op sU)).hom) →
      ∀ (α : (pullback (S.y ∣_ S.U)).obj F ≅ F₀.restrict U₀.ι)
        (F' : S.X.Modules) [F'.IsCoherent],
        (∀ V : S.X.Opens,
          Function.Injective (F'.smul (S.X.presheaf.map V.leTop.op sX)).hom) →
        ∀ (α' : F'.restrict S.U.ι ≅ F) (α₀' : (pullback S.y).obj F' ⟶ F₀),
          (pullback (S.y ∣_ S.U)).map α'.hom ≫ α.hom =
            (pullbackRestrictIso S.y S.U F').hom ≫
              (restrictFunctor U₀.ι).map α₀' →
          IsFiniteLength A
            (S.y.globalSectionsMod F₀ ⧸ (S.y.globalSectionsFunctor.map α₀').hom.range) := sorry

/-- The length defect of a coherent closed-fiber comparison on a punctured local
spectrum is independent of the coherent extension with injective multiplication by
the regular element and of the comparison maps compatible with the fixed
closed-fiber identification through the canonical pullback–restriction isomorphism. -/
theorem comparisonEulerCharacteristic_independent (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hf_regular : IsRegular f) :
    let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
    let U₀ := S.y ⁻¹ᵁ S.U
    let sX := (Scheme.ΓSpecIso (CommRingCat.of A)).inv f
    let sU := S.U.ι.appTop sX
    ∀ (F : S.U.toScheme.Modules) (F₀ : S.Y.Modules) [F.IsCoherent] [F₀.IsCoherent],
      (∀ V : S.U.toScheme.Opens, Function.Injective
        (F.smul (S.U.toScheme.presheaf.map V.leTop.op sU)).hom) →
      ∀ (α : (pullback (S.y ∣_ S.U)).obj F ≅ F₀.restrict U₀.ι)
        (F₁ : S.X.Modules) [F₁.IsCoherent],
        (∀ V : S.X.Opens,
          Function.Injective (F₁.smul (S.X.presheaf.map V.leTop.op sX)).hom) →
        ∀ (α₁ : F₁.restrict S.U.ι ≅ F) (β₁ : (pullback S.y).obj F₁ ⟶ F₀),
          (pullback (S.y ∣_ S.U)).map α₁.hom ≫ α.hom =
            (pullbackRestrictIso S.y S.U F₁).hom ≫
              (restrictFunctor U₀.ι).map β₁ →
          ∀ (F₂ : S.X.Modules) [F₂.IsCoherent],
            (∀ V : S.X.Opens,
              Function.Injective (F₂.smul (S.X.presheaf.map V.leTop.op sX)).hom) →
            ∀ (α₂ : F₂.restrict S.U.ι ≅ F) (β₂ : (pullback S.y).obj F₂ ⟶ F₀),
              (pullback (S.y ∣_ S.U)).map α₂.hom ≫ α.hom =
                (pullbackRestrictIso S.y S.U F₂).hom ≫
                  (restrictFunctor U₀.ι).map β₂ →
              sectionLengthDefect S.y β₁ = sectionLengthDefect S.y β₂ := sorry

end AlgebraicGeometry.Scheme.Modules
