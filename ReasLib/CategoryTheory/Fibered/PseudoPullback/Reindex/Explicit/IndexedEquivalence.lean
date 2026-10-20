/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Reindex.Explicit.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Reindex.Explicit.Equivalence

import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open Opposite
open scoped CategoricalPullback CategoryTheory.Bicategory

universe u v uX uY uS vX vY vS

namespace CategoryTheory

namespace BasedCategory.PseudoPullback.Fiber.reindex.indexed

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}

/-- Identity coherence for the indexed equivalence between actual pseudo-pullback fibers and
their categorical-pullback models. -/
theorem functor.naturality.id
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χP : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.Cleavage)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U : C}
    (P : Functor.Fiber
      (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p U) :
    (Fiber.comparison F.toBasedFunctor G.toBasedFunctor U).map
          ((χP.toPseudofunctor.mapIdOp U).inv.toNatTrans.app P) ≫
        (Fiber.reindex.iso F G χP χX χY χS (𝟙 U)).hom.app P =
      ((BasedCategory.PseudoPullback.reindex.explicit.pseudofunctor F G χX χY χS).mapIdOp'
        ((𝟭 C).obj U) ((𝟭 C).map (𝟙 U))
        ((𝟭 C).map_id U)).inv.toNatTrans.app
          ((Fiber.comparison F.toBasedFunctor G.toBasedFunctor U).obj P) := sorry

/-- Composition coherence for the indexed equivalence between actual pseudo-pullback fibers
and their categorical-pullback models. -/
theorem functor.naturality.comp
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χP : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.Cleavage)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : Functor.Fiber
      (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p U) :
    (Fiber.reindex.iso F G χP χX χY χS (g ≫ f)).hom.app P ≫
        ((BasedCategory.PseudoPullback.reindex.explicit.pseudofunctor F G χX χY χS).mapCompOp'
          ((𝟭 C).map f) ((𝟭 C).map g) ((𝟭 C).map (g ≫ f))
          ((𝟭 C).map_comp g f).symm).hom.toNatTrans.app
            ((Fiber.comparison F.toBasedFunctor G.toBasedFunctor U).obj P) =
      (Fiber.comparison F.toBasedFunctor G.toBasedFunctor W).map
          ((χP.toPseudofunctor.mapCompOp f g).hom.toNatTrans.app P) ≫
        (Fiber.reindex.iso F G χP χX χY χS g).hom.app
          ((χP.toPseudofunctor.map f.op.toLoc).toFunctor.obj P) ≫
        ((BasedCategory.PseudoPullback.reindex.explicit.pseudofunctor F G χX χY χS).map
          ((𝟭 C).map g).op.toLoc).toFunctor.map
            ((Fiber.reindex.iso F G χP χX χY χS f).hom.app P) := sorry

/-- The comparison functors from actual pseudo-pullback fibers to the categorical-pullback
models, each an equivalence, form a coherent indexed functor over `𝟭 C`. -/
@[stacks 0040 "indexed equivalence for pseudo-pullback fibers"]
noncomputable def functor
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χP : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.Cleavage)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage) :
    Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor (𝟭 C)
      χP.toPseudofunctor (BasedCategory.PseudoPullback.reindex.explicit.pseudofunctor F G χX χY χS) where
  app U := (Fiber.comparison F.toBasedFunctor G.toBasedFunctor U)
  naturality f := Fiber.reindex.iso F G χP χX χY χS f
  naturality_id _ P :=
    functor.naturality.id F G χP χX χY χS P
  naturality_comp f g P :=
    functor.naturality.comp F G χP χX χY χS f g P

/-- Components of the actual-to-modeled indexed functor are the canonical comparison functors;
each component is an equivalence. -/
@[simp]
theorem functor.app
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χP : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.Cleavage)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage) (U : C) :
    (functor F G χP χX χY χS).app U =
      (Fiber.comparison F.toBasedFunctor G.toBasedFunctor U) := sorry

/-- Naturality of the actual-to-modeled indexed functor is the canonical reindexing
comparison. -/
@[simp]
theorem functor.naturality
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χP : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.Cleavage)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V : C} (f : V ⟶ U) :
    (functor F G χP χX χY χS).naturality f =
      Fiber.reindex.iso F G χP χX χY χS f := sorry

/-- Transport of a morphism between two restrictions through the actual-to-modeled indexed
functor is conjugation by its two reindexing comparisons. -/
@[simp]
theorem functor.mapHom
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χP : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.Cleavage)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {P : Functor.Fiber
      (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p U₁}
    {Q : Functor.Fiber
      (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p U₂}
    (φ : (χP.reindex f₁).obj P ⟶ (χP.reindex f₂).obj Q) :
    (functor F G χP χX χY χS).mapHom f₁ f₂ φ =
      (Fiber.reindex.iso F G χP χX χY χS f₁).inv.app P ≫
        (Fiber.comparison F.toBasedFunctor G.toBasedFunctor V).map φ ≫
        (Fiber.reindex.iso F G χP χX χY χS f₂).hom.app Q := sorry

/-- The indexed comparison from actual pseudo-pullback fibers to their categorical-pullback
models is an equivalence on every fiber. -/
instance functor.isFiberwiseEquivalence
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χP : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.Cleavage)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage) :
    (functor F G χP χX χY χS).FiberwiseEquivalence := sorry

namespace fst

/-- Compatibility with reindexing of the componentwise identification between the first
projection of the modeled fiber equivalence and the actual first projection. -/
theorem naturality
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χP : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.Cleavage)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V : C} (f : V ⟶ U)
    (P : Functor.Fiber
      (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p U) :
    (((functor F G χP χX χY χS).comp
          (BasedCategory.PseudoPullback.reindex.explicit.fst.indexedFunctor F G χX χY χS)).naturality f).hom.app P ≫
        (χX.toPseudofunctor.map ((𝟭 C).map f).op.toLoc).toFunctor.map
          ((Fiber.comparison.fstIso
            F.toBasedFunctor G.toBasedFunctor U).hom.app P) =
      (Fiber.comparison.fstIso
          F.toBasedFunctor G.toBasedFunctor V).hom.app
            ((χP.toPseudofunctor.map f.op.toLoc).toFunctor.obj P) ≫
        ((CartesianBasedFunctor.Indexed.explicit.functor
          (cartesianFst.ofCleavage F G χX χY) χP χX).naturality f).hom.app P := sorry

/-- The first projection of the modeled fiber equivalence agrees, as an indexed functor, with
the actual first projection of the fibred pseudo-pullback. -/
@[stacks 0040 "indexed first-projection compatibility for pseudo-pullback fibers"]
noncomputable def iso
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χP : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.Cleavage)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage) :
    (functor F G χP χX χY χS).comp
        (BasedCategory.PseudoPullback.reindex.explicit.fst.indexedFunctor F G χX χY χS) ≅
      CartesianBasedFunctor.Indexed.explicit.functor
        (cartesianFst.ofCleavage F G χX χY) χP χX :=
  Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.mkIso
    (fun U ↦ Fiber.comparison.fstIso
      F.toBasedFunctor G.toBasedFunctor U)
    (fun f P ↦ naturality
      F G χP χX χY χS f P)

/-- Components of the indexed first-projection comparison are the canonical first-projection
identifications of the fiber equivalences. -/
@[simp]
theorem iso.app
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χP : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.Cleavage)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    (U : C) :
    Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.isoApp
        (iso F G χP χX χY χS) U =
      Fiber.comparison.fstIso
        F.toBasedFunctor G.toBasedFunctor U := sorry

end fst

namespace snd

/-- Compatibility with reindexing of the componentwise identification between the second
projection of the modeled fiber equivalence and the actual second projection. -/
theorem naturality
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χP : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.Cleavage)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V : C} (f : V ⟶ U)
    (P : Functor.Fiber
      (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p U) :
    (((functor F G χP χX χY χS).comp
          (BasedCategory.PseudoPullback.reindex.explicit.snd.indexedFunctor F G χX χY χS)).naturality f).hom.app P ≫
        (χY.toPseudofunctor.map ((𝟭 C).map f).op.toLoc).toFunctor.map
          ((Fiber.comparison.sndIso
            F.toBasedFunctor G.toBasedFunctor U).hom.app P) =
      (Fiber.comparison.sndIso
          F.toBasedFunctor G.toBasedFunctor V).hom.app
            ((χP.toPseudofunctor.map f.op.toLoc).toFunctor.obj P) ≫
        ((CartesianBasedFunctor.Indexed.explicit.functor
          (cartesianSnd.ofCleavage F G χX χY) χP χY).naturality f).hom.app P := sorry

/-- The second projection of the modeled fiber equivalence agrees, as an indexed functor, with
the actual second projection of the fibred pseudo-pullback. -/
@[stacks 0040 "indexed second-projection compatibility for pseudo-pullback fibers"]
noncomputable def iso
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χP : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.Cleavage)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage) :
    (functor F G χP χX χY χS).comp
        (BasedCategory.PseudoPullback.reindex.explicit.snd.indexedFunctor F G χX χY χS) ≅
      CartesianBasedFunctor.Indexed.explicit.functor
        (cartesianSnd.ofCleavage F G χX χY) χP χY :=
  Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.mkIso
    (fun U ↦ Fiber.comparison.sndIso
      F.toBasedFunctor G.toBasedFunctor U)
    (fun f P ↦ naturality
      F G χP χX χY χS f P)

/-- Components of the indexed second-projection comparison are the canonical second-projection
identifications of the fiber equivalences. -/
@[simp]
theorem iso.app
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χP : (PseudoPullback F.toBasedFunctor G.toBasedFunctor).p.Cleavage)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    (U : C) :
    Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.isoApp
        (iso F G χP χX χY χS) U =
      Fiber.comparison.sndIso
        F.toBasedFunctor G.toBasedFunctor U := sorry

end snd

end BasedCategory.PseudoPullback.Fiber.reindex.indexed

end CategoryTheory
