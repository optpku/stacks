/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudofunctor.Lift.Projections
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudofunctor.Lift.Hom
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudofunctor.Cone
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalence for Pointwise Categorical Pullback Cones

This leaf packages projection and lifting into the category-level equivalence for pointwise
categorical pullbacks, including its unit, counit, and equivalence instances.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback Opposite
open scoped CategoricalPullback CategoryTheory.Bicategory

universe uC vC uD vD uE vE uF vF uG vG uH vH uK vK

namespace CategoryTheory

namespace Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {E : Type uE} [Category.{vE} E]
variable {u : C ⥤ D} {v : E ⥤ C}
variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF}}
variable {G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vG, uG}}
variable {H : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vH, uH}}

variable (K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}) in
/-- Compatible pairs of indexed functors lift functorially to indexed functors into the
pointwise categorical pullback. -/
@[stacks 0040 "functorial lift to a pointwise categorical pseudo-pullback"]
noncomputable def Pullback.Lift.functor
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H) :
    ((postcomp v K L) ⊡ (postcomp v K R)) ⥤
      IndexedFunctor v K (Pullback.pseudofunctor L R) where
  obj P := Pullback.Lift.ofCone L R P.fst P.snd P.iso
  map φ := Pullback.Lift.Hom.map L R φ
  map_id P := Pullback.Lift.Hom.map.id L R P
  map_comp φ ψ := Pullback.Lift.Hom.map.comp L R φ ψ

/-- The object action of pointwise-pullback lifting is the universal indexed lift. -/
@[simp]
theorem Pullback.Lift.functor.obj
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (P : (postcomp v K L) ⊡ (postcomp v K R)) :
    (Pullback.Lift.functor K L R).obj P =
      Pullback.Lift.ofCone L R P.fst P.snd P.iso := sorry

/-- The morphism action of pointwise-pullback lifting is the induced indexed modification. -/
@[simp]
theorem Pullback.Lift.functor.map
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {P Q : (postcomp v K L) ⊡ (postcomp v K R)} (φ : P ⟶ Q) :
    (Pullback.Lift.functor K L R).map φ = Pullback.Lift.Hom.map L R φ := sorry

/-- The component natural isomorphism from an indexed functor into the pointwise pullback to the
lift reconstructed from its projected cone. -/
@[stacks 0040 "fiberwise unit of the pointwise categorical pseudo-pullback equivalence"]
noncomputable def Pullback.equivalence.unitIsoApp
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (T : IndexedFunctor v K (Pullback.pseudofunctor L R)) (U : E) :
    T.app U ≅
      ((Pullback.Cone.functor K L R ⋙ Pullback.Lift.functor K L R).obj T).app U :=
  (CategoricalPullback.functorEquiv (L.app (v.obj U)) (R.app (v.obj U))
    (K.obj (LocallyDiscrete.mk (op U)))).unitIso.app (T.app U)

/-- The first projection of the forward unit component is the identity. -/
@[simp]
theorem Pullback.equivalence.unitIsoApp.hom.fst
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (T : IndexedFunctor v K (Pullback.pseudofunctor L R))
    (U : E) (x : K.obj (LocallyDiscrete.mk (op U))) :
    ((Pullback.equivalence.unitIsoApp L R T U).hom.app x).fst =
      𝟙 ((T.app U).obj x).fst := sorry

/-- The second projection of the forward unit component is the identity. -/
@[simp]
theorem Pullback.equivalence.unitIsoApp.hom.snd
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (T : IndexedFunctor v K (Pullback.pseudofunctor L R))
    (U : E) (x : K.obj (LocallyDiscrete.mk (op U))) :
    ((Pullback.equivalence.unitIsoApp L R T U).hom.app x).snd =
      𝟙 ((T.app U).obj x).snd := sorry

/-- The first projection of the inverse unit component is the identity. -/
@[simp]
theorem Pullback.equivalence.unitIsoApp.inv.fst
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (T : IndexedFunctor v K (Pullback.pseudofunctor L R))
    (U : E) (x : K.obj (LocallyDiscrete.mk (op U))) :
    ((Pullback.equivalence.unitIsoApp L R T U).inv.app x).fst =
      𝟙 ((T.app U).obj x).fst := sorry

/-- The second projection of the inverse unit component is the identity. -/
@[simp]
theorem Pullback.equivalence.unitIsoApp.inv.snd
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (T : IndexedFunctor v K (Pullback.pseudofunctor L R))
    (U : E) (x : K.obj (LocallyDiscrete.mk (op U))) :
    ((Pullback.equivalence.unitIsoApp L R T U).inv.app x).snd =
      𝟙 ((T.app U).obj x).snd := sorry

/-- The component unit isomorphisms commute with reindexing along the cone base functor. -/
theorem Pullback.equivalence.unitIsoApp.naturality
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (T : IndexedFunctor v K (Pullback.pseudofunctor L R))
    {U V : E} (f : V ⟶ U) (x : K.obj (LocallyDiscrete.mk (op U))) :
    (T.naturality f).hom.app x ≫
        ((Pullback.pseudofunctor L R).map (v.map f).op.toLoc).toFunctor.map
          ((Pullback.equivalence.unitIsoApp L R T U).hom.app x) =
      (Pullback.equivalence.unitIsoApp L R T V).hom.app
          ((K.map f.op.toLoc).toFunctor.obj x) ≫
        (((Pullback.Cone.functor K L R ⋙
          Pullback.Lift.functor K L R).obj T).naturality f).hom.app x := sorry

/-- An indexed functor into a pointwise pullback is canonically isomorphic to the lift
reconstructed from its projected cone. -/
@[stacks 0040 "unit component of the pointwise categorical pseudo-pullback equivalence"]
noncomputable def Pullback.equivalence.unitComponent
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (T : IndexedFunctor v K (Pullback.pseudofunctor L R)) :
    T ≅ (Pullback.Cone.functor K L R ⋙ Pullback.Lift.functor K L R).obj T :=
  IndexedFunctor.mkIso
    (Pullback.equivalence.unitIsoApp L R T)
    (fun f x ↦ Pullback.equivalence.unitIsoApp.naturality L R T f x)

/-- Components of the reconstruction comparison are the fiberwise pullback unit components. -/
@[simp]
theorem Pullback.equivalence.unitComponent.app
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (T : IndexedFunctor v K (Pullback.pseudofunctor L R)) (U : E) :
    IndexedFunctor.isoApp (Pullback.equivalence.unitComponent L R T) U =
      Pullback.equivalence.unitIsoApp L R T U := sorry

/-- The reconstruction comparison is natural in the indexed functor. -/
theorem Pullback.equivalence.unitComponent.naturality
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {T S : IndexedFunctor v K (Pullback.pseudofunctor L R)} (α : T ⟶ S) :
    α ≫ (Pullback.equivalence.unitComponent L R S).hom =
      (Pullback.equivalence.unitComponent L R T).hom ≫
        (Pullback.Cone.functor K L R ⋙ Pullback.Lift.functor K L R).map α := sorry

variable (K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}) in
/-- The identity on indexed functors into the pointwise pullback is naturally isomorphic to
projection followed by lifting. -/
@[stacks 0040 "unit of the pointwise categorical pseudo-pullback equivalence"]
noncomputable def Pullback.equivalence.unit
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H) :
    𝟭 (IndexedFunctor v K (Pullback.pseudofunctor L R)) ≅
      Pullback.Cone.functor K L R ⋙ Pullback.Lift.functor K L R :=
  NatIso.ofComponents
    (Pullback.equivalence.unitComponent L R)
    (fun α ↦ Pullback.equivalence.unitComponent.naturality L R α)

/-- Compatibility of the projection comparisons identifying a lifted cone with its source. -/
theorem Pullback.equivalence.counitComponent.w
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (P : (postcomp v K L) ⊡ (postcomp v K R)) :
    (postcomp v K L).map
          (Pullback.Lift.Fst.iso L R P.fst P.snd P.iso).hom ≫
        P.iso.hom =
      (Pullback.Cone.iso L R
          (Pullback.Lift.ofCone L R P.fst P.snd P.iso)).hom ≫
        (postcomp v K R).map
          (Pullback.Lift.Snd.iso L R P.fst P.snd P.iso).hom := sorry

/-- A compatible pair is canonically isomorphic to the cone obtained by lifting and
reprojecting it. -/
@[stacks 0040 "counit component of the pointwise categorical pseudo-pullback equivalence"]
noncomputable def Pullback.equivalence.counitComponent
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (P : (postcomp v K L) ⊡ (postcomp v K R)) :
    (Pullback.Lift.functor K L R ⋙ Pullback.Cone.functor K L R).obj P ≅ P :=
  CategoricalPullback.mkIso
    (Pullback.Lift.Fst.iso L R P.fst P.snd P.iso)
    (Pullback.Lift.Snd.iso L R P.fst P.snd P.iso)
    (Pullback.equivalence.counitComponent.w L R P)

/-- The first projection of the forward counit component is canonical. -/
@[simp]
theorem Pullback.equivalence.counitComponent.hom.fst
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (P : (postcomp v K L) ⊡ (postcomp v K R)) :
    (Pullback.equivalence.counitComponent L R P).hom.fst =
      (Pullback.Lift.Fst.iso L R P.fst P.snd P.iso).hom := sorry

/-- The second projection of the forward counit component is canonical. -/
@[simp]
theorem Pullback.equivalence.counitComponent.hom.snd
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (P : (postcomp v K L) ⊡ (postcomp v K R)) :
    (Pullback.equivalence.counitComponent L R P).hom.snd =
      (Pullback.Lift.Snd.iso L R P.fst P.snd P.iso).hom := sorry

/-- The first projection of the inverse counit component is canonical. -/
@[simp]
theorem Pullback.equivalence.counitComponent.inv.fst
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (P : (postcomp v K L) ⊡ (postcomp v K R)) :
    (Pullback.equivalence.counitComponent L R P).inv.fst =
      (Pullback.Lift.Fst.iso L R P.fst P.snd P.iso).inv := sorry

/-- The second projection of the inverse counit component is canonical. -/
@[simp]
theorem Pullback.equivalence.counitComponent.inv.snd
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (P : (postcomp v K L) ⊡ (postcomp v K R)) :
    (Pullback.equivalence.counitComponent L R P).inv.snd =
      (Pullback.Lift.Snd.iso L R P.fst P.snd P.iso).inv := sorry

/-- The lifted-and-reprojected comparison is natural in the compatible pair. -/
theorem Pullback.equivalence.counitComponent.naturality
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {P Q : (postcomp v K L) ⊡ (postcomp v K R)} (φ : P ⟶ Q) :
    (Pullback.Lift.functor K L R ⋙ Pullback.Cone.functor K L R).map φ ≫
        (Pullback.equivalence.counitComponent L R Q).hom =
      (Pullback.equivalence.counitComponent L R P).hom ≫ φ := sorry

variable (K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}) in
/-- Lifting compatible indexed functors and projecting them again is naturally isomorphic to
the identity. -/
@[stacks 0040 "counit of the pointwise categorical pseudo-pullback equivalence"]
noncomputable def Pullback.equivalence.counit
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H) :
    Pullback.Lift.functor K L R ⋙ Pullback.Cone.functor K L R ≅
      𝟭 ((postcomp v K L) ⊡ (postcomp v K R)) :=
  NatIso.ofComponents
    (Pullback.equivalence.counitComponent L R)
    (fun φ ↦ Pullback.equivalence.counitComponent.naturality L R φ)

/-- The canonical unit and counit satisfy the triangle identity for the cone functor. -/
theorem Pullback.equivalence.triangle
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (T : IndexedFunctor v K (Pullback.pseudofunctor L R)) :
    (Pullback.Cone.functor K L R).map
          ((Pullback.equivalence.unit K L R).hom.app T) ≫
        (Pullback.equivalence.counit K L R).hom.app
          ((Pullback.Cone.functor K L R).obj T) =
      𝟙 ((Pullback.Cone.functor K L R).obj T) := sorry

variable (K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}) in
/-- Indexed functors into a pointwise categorical pullback are equivalent to compatible pairs
of indexed functors. This is the category-level universal property of
`Pullback.pseudofunctor`. -/
@[stacks 0040 "universal equivalence for a pointwise categorical pseudo-pullback"]
noncomputable def Pullback.equivalence
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H) :
    IndexedFunctor v K (Pullback.pseudofunctor L R) ≌
      ((postcomp v K L) ⊡ (postcomp v K R)) where
  functor := Pullback.Cone.functor K L R
  inverse := Pullback.Lift.functor K L R
  unitIso := Pullback.equivalence.unit K L R
  counitIso := Pullback.equivalence.counit K L R
  functor_unitIso_comp T := Pullback.equivalence.triangle L R T

/-- The forward functor of the universal equivalence is projection to the compatible pair. -/
@[simp]
theorem Pullback.equivalence.functor
    (K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK})
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H) :
    (Pullback.equivalence (v := v) K L R).functor =
      Pullback.Cone.functor (v := v) K L R := sorry

/-- The inverse functor of the universal equivalence is pointwise-pullback lifting. -/
@[simp]
theorem Pullback.equivalence.inverse
    (K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK})
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H) :
    (Pullback.equivalence (v := v) K L R).inverse =
      Pullback.Lift.functor (v := v) K L R := sorry

/-- The unit of the universal equivalence is the reconstruction comparison. -/
@[simp]
theorem Pullback.equivalence.unitIso
    (K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK})
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H) :
    (Pullback.equivalence (v := v) K L R).unitIso =
      Pullback.equivalence.unit (v := v) K L R := sorry

/-- The counit of the universal equivalence is the projection comparison. -/
@[simp]
theorem Pullback.equivalence.counitIso
    (K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK})
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H) :
    (Pullback.equivalence (v := v) K L R).counitIso =
      Pullback.equivalence.counit (v := v) K L R := sorry

/-- Projection from indexed functors into a pointwise pullback is an equivalence. -/
instance Pullback.Cone.functor.isEquivalence
    (K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK})
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H) :
    (Pullback.Cone.functor (v := v) K L R).IsEquivalence := sorry

/-- Pointwise-pullback lifting of compatible indexed functors is an equivalence. -/
instance Pullback.Lift.functor.isEquivalence
    (K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK})
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H) :
    (Pullback.Lift.functor (v := v) K L R).IsEquivalence := sorry

end Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

end CategoryTheory
