module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.SmoothBaseChange
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

/- Lemma 76.25.2 (Normalization commutes with smooth base change).
Let S be a scheme, and let Y₂ ⟶ Y₁ over X₂ ⟶ X₁ be a fibre square of algebraic
spaces over S, with f : Y₁ ⟶ X₁ quasi-compact and quasi-separated and φ : X₂ ⟶ X₁
smooth. Writing Yᵢ ⟶ Xᵢ' ⟶ Xᵢ for the relative normalization of Xᵢ in Yᵢ, one has
X₂' ≅ X₂ ×_{X₁} X₁'. -/
@[stacks 082F] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.existsUnique_isIso_normalizationPullback_of_smooth :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f] [Smooth g],
      ∃! h : Hom.normalization (pullback.snd f g) ⟶
          pullback (Hom.fromNormalization f) g,
        Hom.toNormalization (pullback.snd f g) ≫ h =
            pullbackToNormalization f g ∧
          h ≫ pullback.snd (Hom.fromNormalization f) g =
            Hom.fromNormalization (pullback.snd f g) ∧
          IsIso h)
