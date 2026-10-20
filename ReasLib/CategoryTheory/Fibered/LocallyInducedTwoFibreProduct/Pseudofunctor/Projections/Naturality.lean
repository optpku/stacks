/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Projection
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Pseudofunctor.Projections.Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coherence of locally induced two-fibre-product projection comparisons

The comparison cells respect `2`-morphisms and the identity and composition comparisons of the
source and endpoint pseudofunctors.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open BasedCategory ObjectProperty
open scoped Bicategory BasedFunctor Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]

namespace LocallyInduced.TwoFibreProduct

variable {P : ObjectProperty (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable {Q : Bicategory.HomProperty (fun X : P.FullSubbicategory ↦ X.1)}
variable [Q.IsMultiplicative]
variable [BasedCategory.PseudoPullback.HomProperty.IsClosedUnder Q]
variable [Projections.Has (P := P) (Q := Q)]
variable [Q.IsClosedUnderIsomorphisms]
variable [Projections.IsDetected (P := P) (Q := Q)]

/-- The first-projection comparisons are natural for the `2`-morphism action of the
left-endpoint projection pseudofunctor. -/
theorem pseudofunctor.fstIso.naturality.map₂
    {S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)}
    {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) :
    (pseudofunctor P Q).map₂ Γ ▷ fst T.fst T.snd ≫
        (pseudofunctor.fstIso φ).hom =
      (pseudofunctor.fstIso ψ).hom ≫
        fst S.fst S.snd ◁
          (Bicategory.Cospan.leftProjection
            (Bicategory.LocallyInducedBicategory
              (BasedCategory.{max v vB, max w (max u (max v vB))} C)
              (fun X : P.FullSubbicategory ↦ X.1) Q)).map₂ Γ := sorry

/-- The first-projection comparisons respect the identity comparison cells of the locally
induced two-fibre-product and left-endpoint pseudofunctors. -/
theorem pseudofunctor.fstIso.id
    (S : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)) :
    (pseudofunctor.fstIso (𝟙 S)).hom ≫
          fst S.fst S.snd ◁
            ((Bicategory.Cospan.leftProjection
              (Bicategory.LocallyInducedBicategory
                (BasedCategory.{max v vB, max w (max u (max v vB))} C)
                (fun X : P.FullSubbicategory ↦ X.1) Q)).mapId S).hom =
      ((pseudofunctor P Q).mapId S).hom ▷ fst S.fst S.snd ≫
        (Bicategory.leftUnitor (a := (pseudofunctor P Q).obj S) (b := S.left)
          (fst S.fst S.snd)).hom ≫
          (Bicategory.rightUnitor (a := (pseudofunctor P Q).obj S) (b := S.left)
            (fst S.fst S.snd)).inv := sorry

/-- The first-projection comparisons respect the composition comparison cells of the locally
induced two-fibre-product and left-endpoint pseudofunctors. -/
theorem pseudofunctor.fstIso.comp
    {R S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)}
    (ψ : R ⟶ S) (φ : S ⟶ T) :
    (pseudofunctor.fstIso (ψ ≫ φ)).hom ≫
          fst R.fst R.snd ◁
            ((Bicategory.Cospan.leftProjection
              (Bicategory.LocallyInducedBicategory
                (BasedCategory.{max v vB, max w (max u (max v vB))} C)
                (fun X : P.FullSubbicategory ↦ X.1) Q)).mapComp ψ φ).hom =
      ((pseudofunctor P Q).mapComp ψ φ).hom ▷ fst T.fst T.snd ≫
        (α_ _ _ _).hom ≫
          (pseudofunctor P Q).map ψ ◁ (pseudofunctor.fstIso φ).hom ≫
            (α_ _ _ _).inv ≫
              (pseudofunctor.fstIso ψ).hom ▷
                (Bicategory.Cospan.leftProjection
                  (Bicategory.LocallyInducedBicategory
                    (BasedCategory.{max v vB, max w (max u (max v vB))} C)
                    (fun X : P.FullSubbicategory ↦ X.1) Q)).map φ ≫
                (α_ _ _ _).hom := sorry

/-- The second-projection comparisons are natural for the `2`-morphism action of the
right-endpoint projection pseudofunctor. -/
theorem pseudofunctor.sndIso.naturality.map₂
    {S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)}
    {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) :
    (pseudofunctor P Q).map₂ Γ ▷ snd T.fst T.snd ≫
        (pseudofunctor.sndIso φ).hom =
      (pseudofunctor.sndIso ψ).hom ≫
        snd S.fst S.snd ◁
          (Bicategory.Cospan.rightProjection
            (Bicategory.LocallyInducedBicategory
              (BasedCategory.{max v vB, max w (max u (max v vB))} C)
              (fun X : P.FullSubbicategory ↦ X.1) Q)).map₂ Γ := sorry

/-- The second-projection comparisons respect the identity comparison cells of the locally
induced two-fibre-product and right-endpoint pseudofunctors. -/
theorem pseudofunctor.sndIso.id
    (S : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)) :
    (pseudofunctor.sndIso (𝟙 S)).hom ≫
          snd S.fst S.snd ◁
            ((Bicategory.Cospan.rightProjection
              (Bicategory.LocallyInducedBicategory
                (BasedCategory.{max v vB, max w (max u (max v vB))} C)
                (fun X : P.FullSubbicategory ↦ X.1) Q)).mapId S).hom =
      ((pseudofunctor P Q).mapId S).hom ▷ snd S.fst S.snd ≫
        (Bicategory.leftUnitor (a := (pseudofunctor P Q).obj S) (b := S.right)
          (snd S.fst S.snd)).hom ≫
          (Bicategory.rightUnitor (a := (pseudofunctor P Q).obj S) (b := S.right)
            (snd S.fst S.snd)).inv := sorry

/-- The second-projection comparisons respect the composition comparison cells of the locally
induced two-fibre-product and right-endpoint pseudofunctors. -/
theorem pseudofunctor.sndIso.comp
    {R S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)}
    (ψ : R ⟶ S) (φ : S ⟶ T) :
    (pseudofunctor.sndIso (ψ ≫ φ)).hom ≫
          snd R.fst R.snd ◁
            ((Bicategory.Cospan.rightProjection
              (Bicategory.LocallyInducedBicategory
                (BasedCategory.{max v vB, max w (max u (max v vB))} C)
                (fun X : P.FullSubbicategory ↦ X.1) Q)).mapComp ψ φ).hom =
      ((pseudofunctor P Q).mapComp ψ φ).hom ▷ snd T.fst T.snd ≫
        (α_ _ _ _).hom ≫
          (pseudofunctor P Q).map ψ ◁ (pseudofunctor.sndIso φ).hom ≫
            (α_ _ _ _).inv ≫
              (pseudofunctor.sndIso ψ).hom ▷
                (Bicategory.Cospan.rightProjection
                  (Bicategory.LocallyInducedBicategory
                    (BasedCategory.{max v vB, max w (max u (max v vB))} C)
                    (fun X : P.FullSubbicategory ↦ X.1) Q)).map φ ≫
                (α_ _ _ _).hom := sorry

end LocallyInduced.TwoFibreProduct

end CategoryTheory
