module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Reindex.Explicit.Construction
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudofunctor.Construction
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor
open scoped CategoricalPullback CategoryTheory.Bicategory

universe u v uX uY uS vX vY vS

namespace CategoryTheory

namespace BasedCategory.PseudoPullback.reindex.explicit

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}

/-- The cleavage-explicit fiber specialization of
`Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.Pullback.pseudofunctor`. Its values are the
categorical pullbacks of the two fiber functors and its arrow action is componentwise
reindexing. -/
@[stacks 0040 "explicit-cleavage pointwise fiber-pullback pseudofunctor"]
noncomputable def pseudofunctor
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage) :
    LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat :=
  Pullback.pseudofunctor
    (CartesianBasedFunctor.Indexed.explicit.functor F χX χS)
    (CartesianBasedFunctor.Indexed.explicit.functor G χY χS)

/-- The modeled fiber-pullback pseudofunctor sends `U` to the categorical pullback of the two
fiber functors over `U`. -/
@[simp]
theorem pseudofunctor.obj
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage) (U : C) :
    (pseudofunctor F G χX χY χS).obj
        (LocallyDiscrete.mk (op U)) =
      Cat.of ((F.fiberFunctor U) ⊡ (G.fiberFunctor U)) := sorry

/-- The arrow action of the modeled fiber-pullback pseudofunctor is componentwise
reindexing. -/
@[simp]
theorem pseudofunctor.map.toFunctor
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V : C} (f : V ⟶ U) :
    ((pseudofunctor F G χX χY χS).map f.op.toLoc).toFunctor =
      BasedCategory.PseudoPullback.reindex.explicit.functor F G χX χY χS f := sorry

/-- Objectwise action of the modeled fiber-pullback pseudofunctor is componentwise
reindexing. -/
@[simp]
theorem pseudofunctor.map.obj
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V : C} (f : V ⟶ U)
    (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    ((pseudofunctor F G χX χY χS).map f.op.toLoc).toFunctor.obj P =
      (BasedCategory.PseudoPullback.reindex.explicit.functor F G χX χY χS f).obj P := sorry

/-- Morphismwise action of the modeled fiber-pullback pseudofunctor is componentwise
reindexing. -/
@[simp]
theorem pseudofunctor.map.hom
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V : C} (f : V ⟶ U)
    {P Q : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)} (φ : P ⟶ Q) :
    ((pseudofunctor F G χX χY χS).map f.op.toLoc).toFunctor.map φ =
      (BasedCategory.PseudoPullback.reindex.explicit.functor F G χX χY χS f).map φ := sorry

/-- The identity constraint of the modeled fiber-pullback pseudofunctor is the inverse of the
unit comparison from an object to its identity reindexing. -/
@[simp]
theorem pseudofunctor.mapId.hom.app
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    (U : C) (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    ((pseudofunctor F G χX χY χS).mapIdOp U).hom.toNatTrans.app P =
      (idIso F G χX χY χS U).inv.app P := sorry

/-- The inverse identity constraint of the modeled fiber-pullback pseudofunctor is the unit
comparison from an object to its identity reindexing. -/
@[simp]
theorem pseudofunctor.mapId.inv.app
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    (U : C) (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    ((pseudofunctor F G χX χY χS).mapIdOp U).inv.toNatTrans.app P =
      (idIso F G χX χY χS U).hom.app P := sorry

/-- The composition constraint of the modeled fiber-pullback pseudofunctor is the canonical
comparison from direct to successive reindexing. -/
@[simp]
theorem pseudofunctor.mapComp.hom.app
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    ((pseudofunctor F G χX χY χS).mapCompOp f g).hom.toNatTrans.app P =
      (mapCompIso F G χX χY χS f g).hom.app P := sorry

/-- The inverse composition constraint of the modeled fiber-pullback pseudofunctor is the
comparison from successive to direct reindexing. -/
@[simp]
theorem pseudofunctor.mapComp.inv.app
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    ((pseudofunctor F G χX χY χS).mapCompOp f g).inv.toNatTrans.app P =
      (mapCompIso F G χX χY χS f g).inv.app P := sorry

/-- The first projections from the modeled fiber pullbacks form an indexed functor to the
left fiber pseudofunctor. -/
@[stacks 0040 "explicit-cleavage first indexed projection from modeled fiber pullbacks"]
noncomputable def fst.indexedFunctor
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage) :
    Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor (𝟭 C)
      (pseudofunctor F G χX χY χS) χX.toPseudofunctor :=
  Pullback.Fst.indexedFunctor
    (CartesianBasedFunctor.Indexed.explicit.functor F χX χS)
    (CartesianBasedFunctor.Indexed.explicit.functor G χY χS)

/-- Components of the first modeled-fiber-pullback projection are the ordinary first
categorical-pullback projections. -/
@[simp]
theorem fst.indexedFunctor.app
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    (U : C) :
    (fst.indexedFunctor F G χX χY χS).app U =
      π₁ (F.fiberFunctor U) (G.fiberFunctor U) := sorry

/-- Naturality of the first modeled-fiber-pullback projection is its canonical first
reindexing comparison. -/
@[simp]
theorem fst.indexedFunctor.naturality
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V : C} (f : V ⟶ U) :
    (fst.indexedFunctor F G χX χY χS).naturality f =
      fst.iso F G χX χY χS f := sorry

/-- Restricted-morphism transport through the first modeled-fiber-pullback projection is first
projection on morphisms. -/
@[simp]
theorem fst.indexedFunctor.mapHom
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {P : (F.fiberFunctor U₁) ⊡ (G.fiberFunctor U₁)}
    {Q : (F.fiberFunctor U₂) ⊡ (G.fiberFunctor U₂)}
    (φ :
      (BasedCategory.PseudoPullback.reindex.explicit.functor F G χX χY χS f₁).obj P ⟶
        (BasedCategory.PseudoPullback.reindex.explicit.functor F G χX χY χS f₂).obj Q) :
    (fst.indexedFunctor F G χX χY χS).mapHom f₁ f₂ φ =
      φ.fst := sorry

/-- The second projections from the modeled fiber pullbacks form an indexed functor to the
right fiber pseudofunctor. -/
@[stacks 0040 "explicit-cleavage second indexed projection from modeled fiber pullbacks"]
noncomputable def snd.indexedFunctor
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage) :
    Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor (𝟭 C)
      (pseudofunctor F G χX χY χS) χY.toPseudofunctor :=
  Pullback.Snd.indexedFunctor
    (CartesianBasedFunctor.Indexed.explicit.functor F χX χS)
    (CartesianBasedFunctor.Indexed.explicit.functor G χY χS)

/-- Components of the second modeled-fiber-pullback projection are the ordinary second
categorical-pullback projections. -/
@[simp]
theorem snd.indexedFunctor.app
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    (U : C) :
    (snd.indexedFunctor F G χX χY χS).app U =
      π₂ (F.fiberFunctor U) (G.fiberFunctor U) := sorry

/-- Naturality of the second modeled-fiber-pullback projection is its canonical second
reindexing comparison. -/
@[simp]
theorem snd.indexedFunctor.naturality
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U V : C} (f : V ⟶ U) :
    (snd.indexedFunctor F G χX χY χS).naturality f =
      snd.iso F G χX χY χS f := sorry

/-- Restricted-morphism transport through the second modeled-fiber-pullback projection is
second projection on morphisms. -/
@[simp]
theorem snd.indexedFunctor.mapHom
    (F : CartesianBasedFunctor X.p S.p) (G : CartesianBasedFunctor Y.p S.p)
    (χX : X.p.Cleavage) (χY : Y.p.Cleavage) (χS : S.p.Cleavage)
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {P : (F.fiberFunctor U₁) ⊡ (G.fiberFunctor U₁)}
    {Q : (F.fiberFunctor U₂) ⊡ (G.fiberFunctor U₂)}
    (φ :
      (BasedCategory.PseudoPullback.reindex.explicit.functor F G χX χY χS f₁).obj P ⟶
        (BasedCategory.PseudoPullback.reindex.explicit.functor F G χX χY χS f₂).obj Q) :
    (snd.indexedFunctor F G χX χY χS).mapHom f₁ f₂ φ =
      φ.snd := sorry

end BasedCategory.PseudoPullback.reindex.explicit

end CategoryTheory
