/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Target.Basic

/-!
# The category of finite-cover saturation targets

This file owns source-free target refinements, their finite-cover request API,
identity and composition, and the resulting category instance.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v q r r' r'' r''' w'

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation
namespace Target

variable {C : Type u} [Category.{v} C]
variable [LocallySmall.{q} C]
variable {J : GrothendieckTopology C}

/-- A source-free finite-cover refinement between two saturation targets. -/
structure Hom
    (A : Target.{u, v, q, r} C)
    (B : Target.{u, v, q, r'} C) where
  /-- The ordered refinement of the two target systems. -/
  refinement : OrderedRefinement A.diagram B.diagram

namespace Hom

variable {A : Target.{u, v, q, r} C}
variable {B : Target.{u, v, q, r'} C}
variable {D : Target.{u, v, q, r''} C}
variable {E : Target.{u, v, q, r'''} C}

/-- The ordered refinement carried by a target morphism. -/
abbrev toRefinement (f : Hom A B) : OrderedRefinement A.diagram B.diagram :=
  f.refinement

/-- Transport a finite-cover request along a target refinement. -/
noncomputable def mapRequest (f : Hom A B) (request : A.Request J) : B.Request J :=
  f.toRefinement.mapRequest request

namespace mapRequest

/-- A realized finite-cover request remains realized after transport along a target
refinement. -/
theorem isRealized (f : Hom A B) (request : A.Request J) :
    request.is_realized → (f.mapRequest request).is_realized := by
  rintro ⟨i, y, hy⟩
  let η := OrderedRefinement.EssentiallySmall.fiberMap f.toRefinement
  refine ⟨i, η.app (request.cover.obj i).left y, ?_⟩
  exact (ConcreteCategory.congr_hom (η.naturality (request.cover.obj i).hom) y).symm.trans
    (congrArg (η.app request.W) hy)

end mapRequest

/-- A target refinement realizes all finite-cover requests already present at its source. -/
def realizesAll (f : Hom A B) : Prop :=
  ∀ request : A.Request J, (f.mapRequest request).is_realized

/-- Realizing every target request is finite-cover lifting by the underlying refinement. -/
theorem realizesAll_iff_finiteCoverLifts (f : Hom A B) :
    f.realizesAll (J := J) ↔
      NatTrans.FiniteCoverLifts.{u, v, q, w'}
        (OrderedRefinement.EssentiallySmall.fiberMap f.toRefinement) J := by
  constructor
  · intro h W 𝒰 _ h𝒰 x
    obtain ⟨i, y, hy⟩ := h (Functor.CoverLift.Request.ofFamily 𝒰 h𝒰 x)
    exact ⟨(Finite.equivFin 𝒰.index).symm i, y, hy⟩
  · intro h request
    let 𝒰 : SemiRepresentableFamily.Over.{w'} request.W :=
      { index := ULift.{w'} (Fin request.n)
        obj := fun i => request.obj i.down }
    have h𝒰 : 𝒰.toSieve ∈ J request.W := by
      have heq : 𝒰.toSieve = request.cover.toSieve :=
        congrArg Sieve.generate
          (Presieve.ofArrows_comp_eq_of_surjective
            (fun i => (request.obj i).hom) ULift.down_surjective)
      exact heq ▸ request.h𝒰
    obtain ⟨i, y, hy⟩ := h 𝒰 h𝒰 request.f
    exact ⟨i.down, y, hy⟩

/-- The identity target refinement. -/
noncomputable def id (A : Target.{u, v, q, r} C) : Hom A A where
  refinement := OrderedRefinement.id A.diagram

/-- Compose source-free target refinements. -/
noncomputable def comp (f : Hom A B) (g : Hom B D) : Hom A D where
  refinement := f.toRefinement.comp g.toRefinement

namespace id

/-- The ordered refinement underlying an identity target morphism is the identity
refinement. -/
@[simp]
theorem toRefinement (A : Target.{u, v, q, r} C) :
    (id A).toRefinement = OrderedRefinement.id A.diagram := rfl

end id

namespace comp

/-- The ordered refinement underlying a composite target morphism is the composite of the
underlying refinements. -/
@[simp]
theorem toRefinement (f : Hom A B) (g : Hom B D) :
    (comp f g).toRefinement = f.toRefinement.comp g.toRefinement := rfl

end comp

/-- Target refinements are determined by their ordered refinement. -/
@[ext]
theorem ext {f g : Hom A B} (h_refinement : f.toRefinement = g.toRefinement) : f = g := by
  cases f
  cases g
  cases h_refinement
  rfl

/-- Compute the fiber map on a generator directly from functoriality of colimits. -/
private theorem fiberMap_mk (f : Hom A B) {U : A.system.indexᵒᵖ} {W : C}
    (a : A.diagram.obj U ⟶ W) :
    (OrderedRefinement.EssentiallySmall.fiberMap f.toRefinement).app W
      (EssentiallySmallFiber.mk a) =
        EssentiallySmallFiber.mk (S := B.diagram) (f.toRefinement.restrictionIso.inv.app U ≫ a) := by
  letI : InitiallySmall.{q} A.system.indexᵒᵖ := initiallySmall_of_essentiallySmall _
  letI : InitiallySmall.{q} B.system.indexᵒᵖ := initiallySmall_of_essentiallySmall _
  letI : HasColimitsOfShape A.system.indexᵒᵖᵒᵖ (Type q) :=
    hasColimitsOfShape_of_finallySmall _ _
  letI : HasColimitsOfShape B.system.indexᵒᵖᵒᵖ (Type q) :=
    hasColimitsOfShape_of_finallySmall _ _
  let j := f.toRefinement.embedding.toOrderHom.toFunctor
  let d := Reindexing.diagramMap j B.diagram f.toRefinement.restrictionIso W
  have h : colimit.ι (Reindexing.fiberDiagram A.diagram W) (op U) ≫
      colimMap d ≫ colimit.pre (Reindexing.fiberDiagram B.diagram W)
        (Reindexing.indexFunctor j) =
      d.app (op U) ≫ colimit.ι (Reindexing.fiberDiagram B.diagram W)
        ((Reindexing.indexFunctor j).obj (op U)) := by
    rw [ι_colimMap_assoc, colimit.ι_pre]
  calc
    _ = colimit.ι (Reindexing.fiberDiagram B.diagram W)
        ((Reindexing.indexFunctor j).obj (op U))
        (d.app (op U) (shrinkYonedaObjObjEquiv.symm a)) :=
      ConcreteCategory.congr_hom h (shrinkYonedaObjObjEquiv.symm a)
    _ = _ := by
      apply congrArg (colimit.ι (Reindexing.fiberDiagram B.diagram W)
        ((Reindexing.indexFunctor j).obj (op U)))
      change (shrinkYoneda.obj W).map
        ((f.toRefinement.restrictionIso.inv.app U).op ≫ 𝟙 _)
          (shrinkYonedaObjObjEquiv.symm a) = _
      rw [Category.comp_id]
      exact shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm _ a

namespace id

/-- Mapping a request through an identity target refinement leaves it unchanged. -/
@[simp]
theorem mapRequest (A : Target.{u, v, q, r} C)
    (request : A.Request J) : Hom.mapRequest (id A) request = request := by
  letI : InitiallySmall.{q} A.system.indexᵒᵖ := initiallySmall_of_essentiallySmall _
  cases request with
  | mk W n obj h𝒰 x =>
    apply congrArg (Functor.CoverLift.Request.mk W n obj h𝒰)
    dsimp only [Functor.CoverLift.Request.W, Functor.CoverLift.Request.f,
      Hom.mapRequest, OrderedRefinement.mapRequest, Functor.CoverLift.Request.map]
    obtain ⟨U, a, rfl⟩ := fiberMk_jointly_surjective (p := A.diagram) x
    change (OrderedRefinement.EssentiallySmall.fiberMap (id A).toRefinement).app W
      (EssentiallySmallFiber.mk a) = EssentiallySmallFiber.mk a
    rw [fiberMap_mk]
    change fiberMk (𝟙 _ ≫ a) = fiberMk a
    rw [Category.id_comp]

end id

namespace comp

/-- Mapping through a composite target refinement agrees with successive transport. -/
@[simp]
theorem mapRequest (f : Hom A B) (g : Hom B D) (request : A.Request J) :
    Hom.mapRequest (comp f g) request =
      Hom.mapRequest g (Hom.mapRequest f request) := by
  letI : InitiallySmall.{q} A.system.indexᵒᵖ := initiallySmall_of_essentiallySmall _
  cases request with
  | mk W n obj h𝒰 x =>
    apply congrArg (Functor.CoverLift.Request.mk W n obj h𝒰)
    dsimp only [Functor.CoverLift.Request.W, Functor.CoverLift.Request.f,
      Hom.mapRequest, OrderedRefinement.mapRequest, Functor.CoverLift.Request.map]
    obtain ⟨U, a, rfl⟩ := fiberMk_jointly_surjective (p := A.diagram) x
    change (OrderedRefinement.EssentiallySmall.fiberMap (comp f g).toRefinement).app W
      (EssentiallySmallFiber.mk a) =
      (OrderedRefinement.EssentiallySmall.fiberMap g.toRefinement).app W
        ((OrderedRefinement.EssentiallySmall.fiberMap f.toRefinement).app W
          (EssentiallySmallFiber.mk a))
    rw [fiberMap_mk, fiberMap_mk, fiberMap_mk]
    change EssentiallySmallFiber.mk (S := D.diagram)
      (((𝟙 _ ≫ g.toRefinement.restrictionIso.inv.app
        (op (f.toRefinement.embedding U.unop))) ≫
          f.toRefinement.restrictionIso.inv.app U) ≫ a) =
      EssentiallySmallFiber.mk (S := D.diagram)
        (g.toRefinement.restrictionIso.inv.app
          (op (f.toRefinement.embedding U.unop)) ≫
            f.toRefinement.restrictionIso.inv.app U ≫ a)
    simp only [Category.id_comp, Category.assoc]

end comp

/-- Composing an identity target refinement on the left leaves a refinement unchanged. -/
theorem id_comp (f : Hom A B) : comp (id A) f = f := by
  apply ext
  apply congrArg (OrderedRefinement.mk f.toRefinement.embedding)
  apply Iso.ext
  apply NatTrans.ext
  funext i
  change 𝟙 _ ≫ f.toRefinement.restrictionIso.hom.app i ≫ 𝟙 _ =
    f.toRefinement.restrictionIso.hom.app i
  simp only [Category.id_comp, Category.comp_id]

/-- Composing an identity target refinement on the right leaves a refinement unchanged. -/
theorem comp_id (f : Hom A B) : comp f (id B) = f := by
  apply ext
  apply congrArg (OrderedRefinement.mk f.toRefinement.embedding)
  apply Iso.ext
  apply NatTrans.ext
  funext i
  change f.toRefinement.restrictionIso.hom.app i ≫ 𝟙 _ ≫ 𝟙 _ =
    f.toRefinement.restrictionIso.hom.app i
  simp only [Category.comp_id]

/-- Composition of source-free target refinements is associative. -/
theorem comp_assoc (f : Hom A B) (g : Hom B D) (h : Hom D E) :
    comp (comp f g) h = comp f (comp g h) := by
  apply ext
  apply congrArg (OrderedRefinement.mk
    ((f.toRefinement.embedding.comp g.toRefinement.embedding).comp h.toRefinement.embedding))
  apply Iso.ext
  apply NatTrans.ext
  funext i
  let a := f.toRefinement.restrictionIso.hom.app i
  let b := g.toRefinement.restrictionIso.hom.app
    (op (f.toRefinement.embedding i.unop))
  let c := h.toRefinement.restrictionIso.hom.app
    (op (g.toRefinement.embedding (f.toRefinement.embedding i.unop)))
  change (a ≫ b ≫ 𝟙 _) ≫ c ≫ 𝟙 _ = a ≫ (b ≫ c ≫ 𝟙 _) ≫ 𝟙 _
  simp only [Category.assoc, Category.comp_id]

end Hom

/-- Saturation targets in one index universe form a category under source-free refinements. -/
noncomputable instance instCategory :
    Category (Target.{u, v, q, r} C) where
  Hom A B := Hom A B
  id A := Hom.id A
  comp f g := Hom.comp f g
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.comp_assoc

end Target
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
