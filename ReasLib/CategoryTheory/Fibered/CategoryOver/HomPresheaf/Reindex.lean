/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.HomPresheaf.Basic
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Cleavage
import Mathlib.Tactic.CrossRefAttribute

/-!
# Reindexing formulas for fiberwise Hom-presheaf maps

This file compares canonical Hom-presheaf values with morphisms between
objects obtained from the selected cleavage, and computes the induced map in
that model.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

open Opposite

namespace Functor

variable {C : Type u} [Category.{v} C]
variable {S : Type uS} [Category.{vS} S]

/-- Evaluation of a fiber Hom-presheaf at a slice object, expressed using
the selected reindexing functor. -/
@[stacks 042V "reindexing model for Hom-presheaf sections"]
noncomputable def FiberPseudofunctor.PresheafHom.reindexEquiv
    (p : S ⥤ C) [p.IsFibered] {U : C} (x y : p.Fiber U) (W : Over U) :
    ((fiberPseudofunctor p).presheafHom x y).obj (op W) ≃
      (W.hom⁎[Cleavage.ofIsFibered p] x ⟶ W.hom⁎[Cleavage.ofIsFibered p] y) :=
  Iso.homCongr ((FiberPseudofunctor.mapIso p W.hom).app x)
    ((FiberPseudofunctor.mapIso p W.hom).app y)

/-- Evaluation of `reindexEquiv` is conjugation by the selected reindexing
comparison isomorphisms. -/
@[stacks 042V "reindexing evaluation formula for Hom-presheaf sections"]
theorem FiberPseudofunctor.PresheafHom.reindexEquiv.apply
    (p : S ⥤ C) [p.IsFibered] {U : C} (x y : p.Fiber U) (W : Over U)
    (f : ((fiberPseudofunctor p).presheafHom x y).obj (op W)) :
    FiberPseudofunctor.PresheafHom.reindexEquiv p x y W f =
      ((FiberPseudofunctor.mapIso p W.hom).app x).inv ≫ f ≫
        ((FiberPseudofunctor.mapIso p W.hom).app y).hom := sorry

/-- Evaluation of the inverse of `reindexEquiv` is reverse conjugation by
the selected reindexing comparison isomorphisms. -/
@[stacks 042V "inverse reindexing evaluation formula"]
theorem FiberPseudofunctor.PresheafHom.reindexEquiv.symm.apply
    (p : S ⥤ C) [p.IsFibered] {U : C} (x y : p.Fiber U) (W : Over U)
    (f : W.hom⁎[Cleavage.ofIsFibered p] x ⟶ W.hom⁎[Cleavage.ofIsFibered p] y) :
    (FiberPseudofunctor.PresheafHom.reindexEquiv p x y W).symm f =
      ((FiberPseudofunctor.mapIso p W.hom).app x).hom ≫ f ≫
        ((FiberPseudofunctor.mapIso p W.hom).app y).inv := sorry

/-- The selected-reindexing interpretation of a raw Hom-presheaf section is
invertible exactly when the raw section is invertible. -/
@[stacks 02ZA "isomorphism criterion for reindexed Hom-presheaf sections"]
theorem FiberPseudofunctor.PresheafHom.reindexEquiv.isIso_iff
    (p : S ⥤ C) [p.IsFibered] {U : C} (x y : p.Fiber U) (W : Over U)
    (f : ((fiberPseudofunctor p).presheafHom x y).obj (op W)) :
    IsIso (FiberPseudofunctor.PresheafHom.reindexEquiv p x y W f) ↔
      IsIso f := sorry

/-- A raw Hom-presheaf representative obtained from a selected fiber morphism
is invertible exactly when that selected morphism is invertible. -/
@[stacks 02ZA "inverse reindexing isomorphism criterion"]
theorem FiberPseudofunctor.PresheafHom.reindexEquiv.symm.isIso_iff
    (p : S ⥤ C) [p.IsFibered] {U : C} (x y : p.Fiber U) (W : Over U)
    (f : W.hom⁎[Cleavage.ofIsFibered p] x ⟶ W.hom⁎[Cleavage.ofIsFibered p] y) :
    IsIso ((FiberPseudofunctor.PresheafHom.reindexEquiv p x y W).symm f) ↔
      IsIso f := sorry

end Functor

namespace FiberedCategoryOver.Hom

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, uS, vS} C}

/-- The target comparison equivalence used to read a component of
`presheafHomMap` in the selected-reindexing model. -/
@[stacks 042V "target reindexing equivalence for Hom-presheaf maps"]
noncomputable def presheafHomMap.targetEquiv
    (F : X ⟶ Y) {U : C} (x y : X.p.Fiber U) (W : Over U) :
    ((fiberFunctor F W.left).obj
          (W.hom⁎[X.chosenCleavage] x) ⟶
        (fiberFunctor F W.left).obj
          (W.hom⁎[X.chosenCleavage] y)) ≃
      ((Functor.fiberPseudofunctor Y.p).presheafHom
        ((fiberFunctor F U).obj x) ((fiberFunctor F U).obj y)).obj (op W) :=
  Iso.homCongr
    (((Functor.FiberPseudofunctor.mapIso Y.p W.hom).app
      ((fiberFunctor F U).obj x) ≪≫ Reindex.mapIso F W.hom x).symm)
    (((Functor.FiberPseudofunctor.mapIso Y.p W.hom).app
      ((fiberFunctor F U).obj y) ≪≫ Reindex.mapIso F W.hom y).symm)

/-- A component of `presheafHomMap` factors through source reindexing, the
fiber functor, and the target comparison equivalence. -/
@[stacks 042V "component formula for fixed-universe Hom-presheaf maps"]
theorem presheafHomMap.app.apply
    (F : X ⟶ Y) {U : C} (x y : X.p.Fiber U) (W : Over U)
    (f : ((Functor.fiberPseudofunctor X.p).presheafHom x y).obj (op W)) :
    (presheafHomMap F x y).app (op W) f =
      presheafHomMap.targetEquiv F x y W
        ((fiberFunctor F W.left).map
          (Functor.FiberPseudofunctor.PresheafHom.reindexEquiv X.p x y W f)) := sorry

end FiberedCategoryOver.Hom

end CategoryTheory
