/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Pseudofunctor.Construction.Action

/-!
# Pointwise composition comparison of the explicit pseudo-pullback pseudofunctor

Component formulas for the composition comparison and its inverse.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open Functor.IsHomLift
open CategoricalPullback
open scoped Bicategory

universe u v w vB

namespace CategoryTheory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]

namespace PseudoPullback

noncomputable section

/-- The forward component of the bundled composition comparison is the bridge transport followed
by the explicit composition component. -/
@[simp]
theorem pseudofunctor.mapComp.hom.app
    {R S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : R ⟶ S) (φ : S ⟶ T) (P : (PseudoPullback R.fst R.snd).obj) :
    ((pseudofunctor C).mapComp ψ φ).hom.toNatTrans.app P =
      (eqToIso (congrArg
        (fun theta : BasedCospanTransform R.fst R.snd T.fst T.snd =>
          _root_.CategoryTheory.BasedCategory.PseudoPullback.map theta)
        (Bicategory.Cospan.Hom.toBasedTransform.comp ψ φ))).hom.toNatTrans.app P ≫
        (mapComp.component
          (Bicategory.Cospan.Hom.toBasedTransform ψ)
          (Bicategory.Cospan.Hom.toBasedTransform φ) P).hom := sorry

/-- The inverse component of the bundled composition comparison is the inverse explicit component
followed by the inverse bridge transport. -/
@[simp]
theorem pseudofunctor.mapComp.inv.app
    {R S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : R ⟶ S) (φ : S ⟶ T) (P : (PseudoPullback R.fst R.snd).obj) :
    ((pseudofunctor C).mapComp ψ φ).inv.toNatTrans.app P =
      (mapComp.component
        (Bicategory.Cospan.Hom.toBasedTransform ψ)
        (Bicategory.Cospan.Hom.toBasedTransform φ) P).inv ≫
        (eqToIso (congrArg
          (fun theta : BasedCospanTransform R.fst R.snd T.fst T.snd =>
            _root_.CategoryTheory.BasedCategory.PseudoPullback.map theta)
          (Bicategory.Cospan.Hom.toBasedTransform.comp ψ φ))).inv.toNatTrans.app P := sorry

/-- The base component of the forward bundled composition comparison is the identity. -/
@[simp]
theorem pseudofunctor.mapComp.hom.app.base
    {R S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : R ⟶ S) (φ : S ⟶ T) (P : (PseudoPullback R.fst R.snd).obj) :
    baseMap (((pseudofunctor C).mapComp ψ φ).hom.toNatTrans.app P) =
      𝟙 (baseObj (((pseudofunctor C).map ψ ⋙ (pseudofunctor C).map φ).obj P)) := sorry

/-- The first component of the forward bundled composition comparison is the identity. -/
@[simp]
theorem pseudofunctor.mapComp.hom.app.fst
    {R S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : R ⟶ S) (φ : S ⟶ T) (P : (PseudoPullback R.fst R.snd).obj) :
    fstMap (((pseudofunctor C).mapComp ψ φ).hom.toNatTrans.app P) =
      𝟙 (fstObj (((pseudofunctor C).map ψ ⋙ (pseudofunctor C).map φ).obj P)) := sorry

/-- The second component of the forward bundled composition comparison is the identity. -/
@[simp]
theorem pseudofunctor.mapComp.hom.app.snd
    {R S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : R ⟶ S) (φ : S ⟶ T) (P : (PseudoPullback R.fst R.snd).obj) :
    sndMap (((pseudofunctor C).mapComp ψ φ).hom.toNatTrans.app P) =
      𝟙 (sndObj (((pseudofunctor C).map ψ ⋙ (pseudofunctor C).map φ).obj P)) := sorry

/-- The base component of the inverse bundled composition comparison is the identity. -/
@[simp]
theorem pseudofunctor.mapComp.inv.app.base
    {R S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : R ⟶ S) (φ : S ⟶ T) (P : (PseudoPullback R.fst R.snd).obj) :
    baseMap (((pseudofunctor C).mapComp ψ φ).inv.toNatTrans.app P) =
      𝟙 (baseObj (((pseudofunctor C).map ψ ⋙ (pseudofunctor C).map φ).obj P)) := sorry

/-- The first component of the inverse bundled composition comparison is the identity. -/
@[simp]
theorem pseudofunctor.mapComp.inv.app.fst
    {R S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : R ⟶ S) (φ : S ⟶ T) (P : (PseudoPullback R.fst R.snd).obj) :
    fstMap (((pseudofunctor C).mapComp ψ φ).inv.toNatTrans.app P) =
      𝟙 (fstObj (((pseudofunctor C).map ψ ⋙ (pseudofunctor C).map φ).obj P)) := sorry

/-- The second component of the inverse bundled composition comparison is the identity. -/
@[simp]
theorem pseudofunctor.mapComp.inv.app.snd
    {R S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : R ⟶ S) (φ : S ⟶ T) (P : (PseudoPullback R.fst R.snd).obj) :
    sndMap (((pseudofunctor C).mapComp ψ φ).inv.toNatTrans.app P) =
      𝟙 (sndObj (((pseudofunctor C).map ψ ⋙ (pseudofunctor C).map φ).obj P)) := sorry

/-- Every forward packaged composition-comparison component of the explicit pseudo-pullback
pseudofunctor is vertical over the identity common-base map. -/
theorem pseudofunctor.mapComp.hom.app.isHomLift
    {R S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : R ⟶ S) (φ : S ⟶ T) (P : (PseudoPullback R.fst R.snd).obj) :
    (PseudoPullback T.fst T.snd).p.IsHomLift
      (𝟙 ((PseudoPullback R.fst R.snd).p.obj P))
      (((pseudofunctor C).mapComp ψ φ).hom.toNatTrans.app P) := sorry

/-- Every inverse packaged composition-comparison component of the explicit pseudo-pullback
pseudofunctor is vertical over the identity common-base map. -/
theorem pseudofunctor.mapComp.inv.app.isHomLift
    {R S T : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (ψ : R ⟶ S) (φ : S ⟶ T) (P : (PseudoPullback R.fst R.snd).obj) :
    (PseudoPullback T.fst T.snd).p.IsHomLift
      (𝟙 ((PseudoPullback R.fst R.snd).p.obj P))
      (((pseudofunctor C).mapComp ψ φ).inv.toNatTrans.app P) := sorry

end

end PseudoPullback

end BasedCategory

end CategoryTheory
