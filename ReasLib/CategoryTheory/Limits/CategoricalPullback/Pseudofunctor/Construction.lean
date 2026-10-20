/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudofunctor.Reindex.Coherence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Construction of Pointwise Categorical Pullback Pseudofunctors

This leaf assembles pointwise reindexing into a pseudofunctor and provides its two
canonical indexed projections.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback Opposite
open scoped CategoricalPullback CategoryTheory.Bicategory

universe uC vC uD vD uF vF uG vG uH vH

namespace CategoryTheory

namespace Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {u : C ⥤ D}
variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF}}
variable {G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vG, uG}}
variable {H : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vH, uH}}

/-- The pointwise categorical pullbacks of two indexed functors into a common target form a
contravariant `Cat`-valued pseudofunctor. -/
@[stacks 0040 "pointwise categorical pseudo-pullback"]
noncomputable def Pullback.pseudofunctor
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H) :
    LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun U ↦ Cat.of ((L.app (unop U)) ⊡ (R.app (unop U))))
    (fun f ↦ (Pullback.Reindex.functor L R f.unop).toCatHom)
    (fun U ↦ Cat.Hom.isoMk (Pullback.Reindex.mapIdIso L R (unop U)))
    (fun f g ↦ Cat.Hom.isoMk (Pullback.Reindex.mapCompIso L R f.unop g.unop))
    (fun f g h ↦ Pullback.Reindex.Coherence.associator L R f g h)
    (fun f ↦ Pullback.Reindex.Coherence.leftUnitor L R f)
    (fun f ↦ Pullback.Reindex.Coherence.rightUnitor L R f)

/-- The pointwise-pullback pseudofunctor sends `U` to the categorical pullback of the component
functors at `U`. -/
@[simp]
theorem Pullback.pseudofunctor.obj
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (U : C) :
    (Pullback.pseudofunctor L R).obj (LocallyDiscrete.mk (op U)) =
      Cat.of ((L.app U) ⊡ (R.app U)) := sorry

/-- The arrow action of the pointwise-pullback pseudofunctor is its induced pullback
reindexing functor. -/
@[simp]
theorem Pullback.pseudofunctor.map.toFunctor
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V : C} (f : V ⟶ U) :
    ((Pullback.pseudofunctor L R).map f.op.toLoc).toFunctor =
      Pullback.Reindex.functor L R f := sorry

/-- Objectwise action of the pointwise-pullback pseudofunctor. -/
@[simp]
theorem Pullback.pseudofunctor.map.obj
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V : C} (f : V ⟶ U) (P : (L.app U) ⊡ (R.app U)) :
    ((Pullback.pseudofunctor L R).map f.op.toLoc).toFunctor.obj P =
      (Pullback.Reindex.functor L R f).obj P := sorry

/-- Morphismwise action of the pointwise-pullback pseudofunctor. -/
@[simp]
theorem Pullback.pseudofunctor.map.hom
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V : C} (f : V ⟶ U)
    {P Q : (L.app U) ⊡ (R.app U)} (φ : P ⟶ Q) :
    ((Pullback.pseudofunctor L R).map f.op.toLoc).toFunctor.map φ =
      (Pullback.Reindex.functor L R f).map φ := sorry

/-- The identity constraint of the pointwise-pullback pseudofunctor is the inverse of its
object-to-identity-reindexing comparison. -/
@[simp]
theorem Pullback.pseudofunctor.mapId.hom.app
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (U : C) (P : (L.app U) ⊡ (R.app U)) :
    ((Pullback.pseudofunctor L R).mapIdOp U).hom.toNatTrans.app P =
      (Pullback.Reindex.mapIdIso L R U).hom.app P := sorry

/-- The inverse identity constraint of the pointwise-pullback pseudofunctor is its
object-to-identity-reindexing comparison. -/
@[simp]
theorem Pullback.pseudofunctor.mapId.inv.app
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (U : C) (P : (L.app U) ⊡ (R.app U)) :
    ((Pullback.pseudofunctor L R).mapIdOp U).inv.toNatTrans.app P =
      (Pullback.Reindex.mapIdIso L R U).inv.app P := sorry

/-- The composition constraint of the pointwise-pullback pseudofunctor is its direct-to-
successive reindexing comparison. -/
@[simp]
theorem Pullback.pseudofunctor.mapComp.hom.app
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : (L.app U) ⊡ (R.app U)) :
    ((Pullback.pseudofunctor L R).mapCompOp f g).hom.toNatTrans.app P =
      (Pullback.Reindex.mapCompIso L R f g).hom.app P := sorry

/-- The inverse composition constraint of the pointwise-pullback pseudofunctor is its
successive-to-direct reindexing comparison. -/
@[simp]
theorem Pullback.pseudofunctor.mapComp.inv.app
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : (L.app U) ⊡ (R.app U)) :
    ((Pullback.pseudofunctor L R).mapCompOp f g).inv.toNatTrans.app P =
      (Pullback.Reindex.mapCompIso L R f g).inv.app P := sorry

/-- Naturality of the first projection from a pointwise pullback of indexed categories. -/
noncomputable def Pullback.Fst.naturality
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V : C} (f : V ⟶ U) :
    ((Pullback.pseudofunctor L R).map f.op.toLoc).toFunctor ⋙
        π₁ (L.app V) (R.app V) ≅
      π₁ (L.app U) (R.app U) ⋙
        (F.map ((𝟭 C).map f).op.toLoc).toFunctor :=
  Pullback.Reindex.fstIso L R f

/-- Identity coherence for the first indexed projection from a pointwise pullback. -/
theorem Pullback.Fst.naturality.id
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (U : C) (P : (L.app U) ⊡ (R.app U)) :
    (π₁ (L.app U) (R.app U)).map
          (((Pullback.pseudofunctor L R).mapIdOp U).inv.toNatTrans.app P) ≫
        (Pullback.Fst.naturality L R (𝟙 U)).hom.app P =
      (F.mapIdOp' ((𝟭 C).obj U) ((𝟭 C).map (𝟙 U))
        ((𝟭 C).map_id U)).inv.toNatTrans.app P.fst := sorry

/-- Composition coherence for the first indexed projection from a pointwise pullback. -/
theorem Pullback.Fst.naturality.comp
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : (L.app U) ⊡ (R.app U)) :
    (Pullback.Fst.naturality L R (g ≫ f)).hom.app P ≫
        (F.mapCompOp' ((𝟭 C).map f) ((𝟭 C).map g)
          ((𝟭 C).map (g ≫ f))
          ((𝟭 C).map_comp g f).symm).hom.toNatTrans.app P.fst =
      (π₁ (L.app W) (R.app W)).map
          (((Pullback.pseudofunctor L R).mapCompOp f g).hom.toNatTrans.app P) ≫
        (Pullback.Fst.naturality L R g).hom.app
          (((Pullback.pseudofunctor L R).map f.op.toLoc).toFunctor.obj P) ≫
        (F.map ((𝟭 C).map g).op.toLoc).toFunctor.map
          ((Pullback.Fst.naturality L R f).hom.app P) := sorry

/-- The first projections from pointwise categorical pullbacks form an indexed functor to the
left source pseudofunctor. -/
@[stacks 0040 "first indexed projection from a pointwise categorical pseudo-pullback"]
noncomputable def Pullback.Fst.indexedFunctor
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H) :
    IndexedFunctor (𝟭 C) (Pullback.pseudofunctor L R) F where
  app U := π₁ (L.app U) (R.app U)
  naturality f := Pullback.Fst.naturality L R f
  naturality_id U P := Pullback.Fst.naturality.id L R U P
  naturality_comp f g P :=
    Pullback.Fst.naturality.comp L R f g P

/-- Components of the first indexed projection are the ordinary first pullback projections. -/
@[simp]
theorem Pullback.Fst.indexedFunctor.app
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (U : C) :
    (Pullback.Fst.indexedFunctor L R).app U =
      π₁ (L.app U) (R.app U) := sorry

/-- Naturality of the first indexed projection is the canonical first-projection comparison. -/
@[simp]
theorem Pullback.Fst.indexedFunctor.naturality
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V : C} (f : V ⟶ U) :
    (Pullback.Fst.indexedFunctor L R).naturality f =
      Pullback.Reindex.fstIso L R f := sorry

/-- Restricted-morphism transport through the first indexed projection is first projection on
morphisms. -/
@[simp]
theorem Pullback.Fst.indexedFunctor.mapHom
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {P : (L.app U₁) ⊡ (R.app U₁)}
    {Q : (L.app U₂) ⊡ (R.app U₂)}
    (φ :
      (Pullback.Reindex.functor L R f₁).obj P ⟶
        (Pullback.Reindex.functor L R f₂).obj Q) :
    (Pullback.Fst.indexedFunctor L R).mapHom f₁ f₂ φ = φ.fst := sorry

/-- Naturality of the second projection from a pointwise pullback of indexed categories. -/
noncomputable def Pullback.Snd.naturality
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V : C} (f : V ⟶ U) :
    ((Pullback.pseudofunctor L R).map f.op.toLoc).toFunctor ⋙
        π₂ (L.app V) (R.app V) ≅
      π₂ (L.app U) (R.app U) ⋙
        (G.map ((𝟭 C).map f).op.toLoc).toFunctor :=
  Pullback.Reindex.sndIso L R f

/-- Identity coherence for the second indexed projection from a pointwise pullback. -/
theorem Pullback.Snd.naturality.id
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (U : C) (P : (L.app U) ⊡ (R.app U)) :
    (π₂ (L.app U) (R.app U)).map
          (((Pullback.pseudofunctor L R).mapIdOp U).inv.toNatTrans.app P) ≫
        (Pullback.Snd.naturality L R (𝟙 U)).hom.app P =
      (G.mapIdOp' ((𝟭 C).obj U) ((𝟭 C).map (𝟙 U))
        ((𝟭 C).map_id U)).inv.toNatTrans.app P.snd := sorry

/-- Composition coherence for the second indexed projection from a pointwise pullback. -/
theorem Pullback.Snd.naturality.comp
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : (L.app U) ⊡ (R.app U)) :
    (Pullback.Snd.naturality L R (g ≫ f)).hom.app P ≫
        (G.mapCompOp' ((𝟭 C).map f) ((𝟭 C).map g)
          ((𝟭 C).map (g ≫ f))
          ((𝟭 C).map_comp g f).symm).hom.toNatTrans.app P.snd =
      (π₂ (L.app W) (R.app W)).map
          (((Pullback.pseudofunctor L R).mapCompOp f g).hom.toNatTrans.app P) ≫
        (Pullback.Snd.naturality L R g).hom.app
          (((Pullback.pseudofunctor L R).map f.op.toLoc).toFunctor.obj P) ≫
        (G.map ((𝟭 C).map g).op.toLoc).toFunctor.map
          ((Pullback.Snd.naturality L R f).hom.app P) := sorry

/-- The second projections from pointwise categorical pullbacks form an indexed functor to the
right source pseudofunctor. -/
@[stacks 0040 "second indexed projection from a pointwise categorical pseudo-pullback"]
noncomputable def Pullback.Snd.indexedFunctor
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H) :
    IndexedFunctor (𝟭 C) (Pullback.pseudofunctor L R) G where
  app U := π₂ (L.app U) (R.app U)
  naturality f := Pullback.Snd.naturality L R f
  naturality_id U P := Pullback.Snd.naturality.id L R U P
  naturality_comp f g P :=
    Pullback.Snd.naturality.comp L R f g P

/-- Components of the second indexed projection are the ordinary second pullback projections. -/
@[simp]
theorem Pullback.Snd.indexedFunctor.app
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (U : C) :
    (Pullback.Snd.indexedFunctor L R).app U =
      π₂ (L.app U) (R.app U) := sorry

/-- Naturality of the second indexed projection is the canonical second-projection comparison. -/
@[simp]
theorem Pullback.Snd.indexedFunctor.naturality
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V : C} (f : V ⟶ U) :
    (Pullback.Snd.indexedFunctor L R).naturality f =
      Pullback.Reindex.sndIso L R f := sorry

/-- Restricted-morphism transport through the second indexed projection is second projection on
morphisms. -/
@[simp]
theorem Pullback.Snd.indexedFunctor.mapHom
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {P : (L.app U₁) ⊡ (R.app U₁)}
    {Q : (L.app U₂) ⊡ (R.app U₂)}
    (φ :
      (Pullback.Reindex.functor L R f₁).obj P ⟶
        (Pullback.Reindex.functor L R f₂).obj Q) :
    (Pullback.Snd.indexedFunctor L R).mapHom f₁ f₂ φ = φ.snd := sorry

end Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

end CategoryTheory
