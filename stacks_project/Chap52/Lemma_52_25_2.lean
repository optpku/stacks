module

public import stacks_project.Chap52.«52_25_1_1»
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.ComparisonEulerCharacteristic
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry

/- Lemma 52.25.2: The closed-fiber cokernel length minus kernel length of a coherent
triple is independent of the admissible coherent extension and comparison maps. -/
@[stacks 0F25] #check (AlgebraicGeometry.Scheme.Modules.comparisonEulerCharacteristic_independent :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A) (hf_regular : IsRegular f),
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
              sectionLengthDefect S.y β₁ = sectionLengthDefect S.y β₂)
