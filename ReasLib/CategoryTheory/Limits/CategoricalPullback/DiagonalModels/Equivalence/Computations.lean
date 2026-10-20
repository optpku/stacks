/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.DiagonalModels.Equivalence.Construction

/-!
# Computations for the equivalence of concrete diagonal models

Projection formulas for the inverse functor, unit, and counit of the explicit equivalence between
the direct diagonal model and the iterated categorical-pullback model.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Prod
open CategoricalPullback
open scoped CategoricalPullback

universe vC vS uC uS

namespace CategoryTheory.Limits

noncomputable section

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]
variable (G₁ G₂ : C ⥤ S)

namespace CategoricalPullback.DiagonalModel.equivalence

/-- The forward functor of the canonical model equivalence is the specified comparison. -/
@[simp] theorem functor :
    (CategoricalPullback.DiagonalModel.equivalence G₁ G₂).functor =
      CategoricalPullback.DiagonalModel.comparison G₁ G₂ := sorry

/-- The inverse of the canonical model equivalence sends an iterated object to its outer
`C`-object. -/
@[simp] theorem inverse.obj.fst
    (X : CategoricalPullback.DiagonalModel.iterated G₁ G₂) :
    ((CategoricalPullback.DiagonalModel.equivalence G₁ G₂).inverse.obj X).fst = X.snd := sorry

/-- The second object of the canonical inverse is obtained by applying `G₁` to the inner first
object. -/
@[simp] theorem inverse.obj.snd
    (X : CategoricalPullback.DiagonalModel.iterated G₁ G₂) :
    ((CategoricalPullback.DiagonalModel.equivalence G₁ G₂).inverse.obj X).snd =
      G₁.obj X.fst.fst := sorry

/-- The structural isomorphism of the canonical inverse transports both outer components back to
the inner first object. -/
@[simp] theorem inverse.obj.iso
    (X : CategoricalPullback.DiagonalModel.iterated G₁ G₂) :
    ((CategoricalPullback.DiagonalModel.equivalence G₁ G₂).inverse.obj X).iso =
      Iso.prod
        (G₁.mapIso ((CategoryTheory.Prod.fst C C).mapIso X.iso).symm)
        (G₂.mapIso ((CategoryTheory.Prod.snd C C).mapIso X.iso).symm ≪≫ X.fst.iso.symm) := sorry

/-- The first map of the canonical inverse is the outer map of the iterated pullback. -/
@[simp] theorem inverse.map.fst
    {X Y : CategoricalPullback.DiagonalModel.iterated G₁ G₂} (f : X ⟶ Y) :
    ((CategoricalPullback.DiagonalModel.equivalence G₁ G₂).inverse.map f).fst = f.snd := sorry

/-- The second map of the canonical inverse is `G₁` applied to the inner first map. -/
@[simp] theorem inverse.map.snd
    {X Y : CategoricalPullback.DiagonalModel.iterated G₁ G₂} (f : X ⟶ Y) :
    ((CategoricalPullback.DiagonalModel.equivalence G₁ G₂).inverse.map f).snd =
      G₁.map f.fst.fst := sorry

/-- The first component of the diagonal-model equivalence unit is the identity on the
underlying `C`-object. -/
@[simp] theorem unitIso.hom.app.fst
    (X : CategoricalPullback.DiagonalModel.direct G₁ G₂) :
    ((CategoricalPullback.DiagonalModel.equivalence G₁ G₂).unitIso.hom.app X).fst = 𝟙 X.fst := sorry

/-- The second component of the diagonal-model equivalence unit is the inverse of the first
component of the original diagonal structural isomorphism. -/
@[simp] theorem unitIso.hom.app.snd
    (X : CategoricalPullback.DiagonalModel.direct G₁ G₂) :
    ((CategoricalPullback.DiagonalModel.equivalence G₁ G₂).unitIso.hom.app X).snd =
      ((CategoryTheory.Prod.fst S S).mapIso X.iso).inv := sorry

/-- The first component of the inverse diagonal-model equivalence unit is the identity on the
underlying `C`-object. -/
@[simp] theorem unitIso.inv.app.fst
    (X : CategoricalPullback.DiagonalModel.direct G₁ G₂) :
    ((CategoricalPullback.DiagonalModel.equivalence G₁ G₂).unitIso.inv.app X).fst = 𝟙 X.fst := sorry

/-- The second component of the inverse diagonal-model equivalence unit is the first component
of the original diagonal structural isomorphism. -/
@[simp] theorem unitIso.inv.app.snd
    (X : CategoricalPullback.DiagonalModel.direct G₁ G₂) :
    ((CategoricalPullback.DiagonalModel.equivalence G₁ G₂).unitIso.inv.app X).snd =
      ((CategoryTheory.Prod.fst S S).mapIso X.iso).hom := sorry

/-- The first inner component of the diagonal-model equivalence counit is the inverse of the
first component of the iterated model's outer structural isomorphism. -/
@[simp] theorem counitIso.hom.app.fstFst
    (X : CategoricalPullback.DiagonalModel.iterated G₁ G₂) :
    ((CategoricalPullback.DiagonalModel.equivalence G₁ G₂).counitIso.hom.app X).fst.fst =
      ((CategoryTheory.Prod.fst C C).mapIso X.iso).inv := sorry

/-- The second inner component of the diagonal-model equivalence counit is the inverse of the
second component of the iterated model's outer structural isomorphism. -/
@[simp] theorem counitIso.hom.app.fstSnd
    (X : CategoricalPullback.DiagonalModel.iterated G₁ G₂) :
    ((CategoricalPullback.DiagonalModel.equivalence G₁ G₂).counitIso.hom.app X).fst.snd =
      ((CategoryTheory.Prod.snd C C).mapIso X.iso).inv := sorry

/-- The outer component of the diagonal-model equivalence counit is the identity. -/
@[simp] theorem counitIso.hom.app.snd
    (X : CategoricalPullback.DiagonalModel.iterated G₁ G₂) :
    ((CategoricalPullback.DiagonalModel.equivalence G₁ G₂).counitIso.hom.app X).snd = 𝟙 X.snd := sorry

/-- The first inner component of the inverse diagonal-model equivalence counit is the first
component of the iterated model's outer structural isomorphism. -/
@[simp] theorem counitIso.inv.app.fstFst
    (X : CategoricalPullback.DiagonalModel.iterated G₁ G₂) :
    ((CategoricalPullback.DiagonalModel.equivalence G₁ G₂).counitIso.inv.app X).fst.fst =
      ((CategoryTheory.Prod.fst C C).mapIso X.iso).hom := sorry

/-- The second inner component of the inverse diagonal-model equivalence counit is the second
component of the iterated model's outer structural isomorphism. -/
@[simp] theorem counitIso.inv.app.fstSnd
    (X : CategoricalPullback.DiagonalModel.iterated G₁ G₂) :
    ((CategoricalPullback.DiagonalModel.equivalence G₁ G₂).counitIso.inv.app X).fst.snd =
      ((CategoryTheory.Prod.snd C C).mapIso X.iso).hom := sorry

/-- The outer component of the inverse diagonal-model equivalence counit is the identity. -/
@[simp] theorem counitIso.inv.app.snd
    (X : CategoricalPullback.DiagonalModel.iterated G₁ G₂) :
    ((CategoricalPullback.DiagonalModel.equivalence G₁ G₂).counitIso.inv.app X).snd = 𝟙 X.snd := sorry

end CategoricalPullback.DiagonalModel.equivalence

end

end CategoryTheory.Limits
