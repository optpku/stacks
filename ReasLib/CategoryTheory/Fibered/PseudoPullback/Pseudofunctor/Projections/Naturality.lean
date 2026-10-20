/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Pseudofunctor.Projections.Comparison

/-!
# Naturality and coherence of explicit pseudo-pullback projections

The comparison isomorphisms are natural in bundled cospan `2`-cells and compatible with the
identity and composition comparisons.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open BasedNatIso
open Functor.IsHomLift
open Functor.Fiber
open CategoricalPullback
open scoped CategoricalPullback
open scoped Bicategory BasedFunctor Pseudofunctor.StrongTrans

universe u v w vB

namespace CategoryTheory

open Bicategory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]

namespace PseudoPullback

noncomputable section

/-- The first-projection comparisons are `2`-natural in bundled cospan `2`-morphisms. -/
@[reassoc]
theorem pseudofunctor.fstIso.naturality.hom
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) :
    BasedCategory.whiskerRight
          ((pseudofunctor C).map₂ Γ) (fst T.fst T.snd) ≫
        (pseudofunctor.fstIso φ).hom =
      (pseudofunctor.fstIso ψ).hom ≫
        BasedCategory.whiskerLeft (fst S.fst S.snd)
          (Bicategory.Cospan.Hom₂.left Γ) := sorry

/-- The inverse first-projection comparisons are `2`-natural in bundled cospan
`2`-morphisms. -/
@[reassoc]
theorem pseudofunctor.fstIso.naturality.inv
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) :
    BasedCategory.whiskerLeft (fst S.fst S.snd)
          (Bicategory.Cospan.Hom₂.left Γ) ≫
        (pseudofunctor.fstIso φ).inv =
      (pseudofunctor.fstIso ψ).inv ≫
        BasedCategory.whiskerRight
          ((pseudofunctor C).map₂ Γ) (fst T.fst T.snd) := sorry

/-- The second-projection comparisons are `2`-natural in bundled cospan `2`-morphisms. -/
@[reassoc]
theorem pseudofunctor.sndIso.naturality.hom
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) :
    BasedCategory.whiskerRight
          ((pseudofunctor C).map₂ Γ) (snd T.fst T.snd) ≫
        (pseudofunctor.sndIso φ).hom =
      (pseudofunctor.sndIso ψ).hom ≫
        BasedCategory.whiskerLeft (snd S.fst S.snd)
          (Bicategory.Cospan.Hom₂.right Γ) := sorry

/-- The inverse second-projection comparisons are `2`-natural in bundled cospan
`2`-morphisms. -/
@[reassoc]
theorem pseudofunctor.sndIso.naturality.inv
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) :
    BasedCategory.whiskerLeft (snd S.fst S.snd)
          (Bicategory.Cospan.Hom₂.right Γ) ≫
        (pseudofunctor.sndIso φ).inv =
      (pseudofunctor.sndIso ψ).inv ≫
        BasedCategory.whiskerRight
          ((pseudofunctor C).map₂ Γ) (snd T.fst T.snd) := sorry

/-- The first-projection comparisons are natural for the `2`-morphism action of the
left-endpoint projection pseudofunctor. -/
theorem pseudofunctor.fstIso.naturality.map₂
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) :
    (pseudofunctor C).map₂ Γ ▷ fst T.fst T.snd ≫
        (pseudofunctor.fstIso φ).hom =
      (pseudofunctor.fstIso ψ).hom ≫
        fst S.fst S.snd ◁
          (Bicategory.Cospan.leftProjection
            (BasedCategory.{max v vB, max w (max u (max v vB))} C)).map₂ Γ := sorry

/-- The second-projection comparisons are natural for the `2`-morphism action of the
right-endpoint projection pseudofunctor. -/
theorem pseudofunctor.sndIso.naturality.map₂
    {S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) :
    (pseudofunctor C).map₂ Γ ▷ snd T.fst T.snd ≫
        (pseudofunctor.sndIso φ).hom =
      (pseudofunctor.sndIso ψ).hom ≫
        snd S.fst S.snd ◁
          (Bicategory.Cospan.rightProjection
            (BasedCategory.{max v vB, max w (max u (max v vB))} C)).map₂ Γ := sorry

/-- The first-projection comparisons respect the identity comparison cells of the
pseudo-pullback and left-endpoint pseudofunctors. -/
theorem pseudofunctor.fstIso.id
    (S : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)) :
    (pseudofunctor.fstIso (𝟙 S)).hom ≫
          fst S.fst S.snd ◁
            ((Bicategory.Cospan.leftProjection
              (BasedCategory.{max v vB, max w (max u (max v vB))} C)).mapId S).hom =
      ((pseudofunctor C).mapId S).hom ▷ fst S.fst S.snd ≫
        (Bicategory.leftUnitor (a := (pseudofunctor C).obj S) (b := S.left)
          (fst S.fst S.snd)).hom ≫
          (Bicategory.rightUnitor (a := (pseudofunctor C).obj S) (b := S.left)
            (fst S.fst S.snd)).inv := sorry

/-- The first-projection comparisons respect the composition comparison cells of the
pseudo-pullback and left-endpoint pseudofunctors. -/
theorem pseudofunctor.fstIso.comp
    {R S T : Bicategory.Cospan
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : R ⟶ S) (φ : S ⟶ T) :
    (pseudofunctor.fstIso (ψ ≫ φ)).hom ≫
          fst R.fst R.snd ◁
            ((Bicategory.Cospan.leftProjection
              (BasedCategory.{max v vB, max w (max u (max v vB))} C)).mapComp ψ φ).hom =
      ((pseudofunctor C).mapComp ψ φ).hom ▷ fst T.fst T.snd ≫
        (α_ _ _ _).hom ≫
          (pseudofunctor C).map ψ ◁ (pseudofunctor.fstIso φ).hom ≫
            (α_ _ _ _).inv ≫
              (pseudofunctor.fstIso ψ).hom ▷
                (Bicategory.Cospan.leftProjection
                  (BasedCategory.{max v vB, max w (max u (max v vB))} C)).map φ ≫
                (α_ _ _ _).hom := sorry

/-- The second-projection comparisons respect the identity comparison cells of the
pseudo-pullback and right-endpoint pseudofunctors. -/
theorem pseudofunctor.sndIso.id
    (S : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)) :
    (pseudofunctor.sndIso (𝟙 S)).hom ≫
          snd S.fst S.snd ◁
            ((Bicategory.Cospan.rightProjection
              (BasedCategory.{max v vB, max w (max u (max v vB))} C)).mapId S).hom =
      ((pseudofunctor C).mapId S).hom ▷ snd S.fst S.snd ≫
        (Bicategory.leftUnitor (a := (pseudofunctor C).obj S) (b := S.right)
          (snd S.fst S.snd)).hom ≫
          (Bicategory.rightUnitor (a := (pseudofunctor C).obj S) (b := S.right)
            (snd S.fst S.snd)).inv := sorry

/-- The second-projection comparisons respect the composition comparison cells of the
pseudo-pullback and right-endpoint pseudofunctors. -/
theorem pseudofunctor.sndIso.comp
    {R S T : Bicategory.Cospan
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : R ⟶ S) (φ : S ⟶ T) :
    (pseudofunctor.sndIso (ψ ≫ φ)).hom ≫
          snd R.fst R.snd ◁
            ((Bicategory.Cospan.rightProjection
              (BasedCategory.{max v vB, max w (max u (max v vB))} C)).mapComp ψ φ).hom =
      ((pseudofunctor C).mapComp ψ φ).hom ▷ snd T.fst T.snd ≫
        (α_ _ _ _).hom ≫
          (pseudofunctor C).map ψ ◁ (pseudofunctor.sndIso φ).hom ≫
            (α_ _ _ _).inv ≫
              (pseudofunctor.sndIso ψ).hom ▷
                (Bicategory.Cospan.rightProjection
                  (BasedCategory.{max v vB, max w (max u (max v vB))} C)).map φ ≫
                (α_ _ _ _).hom := sorry

end

end PseudoPullback

end BasedCategory

end CategoryTheory
