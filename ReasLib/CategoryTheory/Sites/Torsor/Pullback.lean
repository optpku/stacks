/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import ReasLib.CategoryTheory.Sites.Torsor.IsoClasses

/-!
# Inverse image of torsors on sites

The inverse image of a torsor is obtained by transporting its sheaf action
through the product and coefficient comparisons for sheaf inverse image.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.Sheaf.Torsor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- The sectionwise action of a torsor commutes with restriction on the product sheaf. -/
theorem action_naturality {G : Sheaf J GrpCat.{w}} (P : Torsor G)
    {U V : Cᵒᵖ} (h : U ⟶ V) :
    ((sheafForget J).obj G ⨯ P.carrier).obj.map h ≫
        TypeCat.ofHom (fun p ↦ (P.mulAction V.unop).smul
          ((prod.fst : (sheafForget J).obj G ⨯ P.carrier ⟶
            (sheafForget J).obj G).hom.app V p)
          ((prod.snd : (sheafForget J).obj G ⨯ P.carrier ⟶
            P.carrier).hom.app V p)) =
      TypeCat.ofHom (fun p ↦ (P.mulAction U.unop).smul
          ((prod.fst : (sheafForget J).obj G ⨯ P.carrier ⟶
            (sheafForget J).obj G).hom.app U p)
          ((prod.snd : (sheafForget J).obj G ⨯ P.carrier ⟶
            P.carrier).hom.app U p)) ≫ P.carrier.obj.map h := sorry

/-- The action of a group sheaf on a torsor, as a morphism of sheaves of sets. -/
def action {G : Sheaf J GrpCat.{w}} (P : Torsor G) :
    (sheafForget J).obj G ⨯ P.carrier ⟶ P.carrier :=
  Sheaf.homEquiv.symm
    { app := fun U ↦ TypeCat.ofHom fun p ↦
        (P.mulAction U.unop).smul
          ((prod.fst : (sheafForget J).obj G ⨯ P.carrier ⟶
            (sheafForget J).obj G).hom.app U p)
          ((prod.snd : (sheafForget J).obj G ⨯ P.carrier ⟶
            P.carrier).hom.app U p)
      naturality := fun {_ _} h ↦ action_naturality P h }

variable (K)
variable (f : C ⥤ D) [f.IsContinuous J K]
variable [∀ P : Cᵒᵖ ⥤ Type w, f.op.HasLeftKanExtension P]
variable [∀ P : Cᵒᵖ ⥤ GrpCat.{w}, f.op.HasLeftKanExtension P]
variable [HasWeakSheafify K (Type w)] [HasWeakSheafify K GrpCat.{w}]
variable [J.HasSheafCompose (CategoryTheory.forget GrpCat.{w})]
variable [K.HasSheafCompose (CategoryTheory.forget GrpCat.{w})]
variable [(CategoryTheory.forget GrpCat.{w}).PreservesLeftKanExtensions f.op]
variable [K.PreservesSheafification (CategoryTheory.forget GrpCat.{w})]
variable [hLeftExact : PreservesFiniteLimits (f.sheafPullback (Type w) J K)]

/-- Inverse image transports the action through the product and coefficient comparisons. -/
def pullbackAction (G : Sheaf J GrpCat.{w}) (P : Torsor G) :
    (sheafForget K).obj ((f.sheafPullback GrpCat.{w} J K).obj G) ⨯
        (f.sheafPullback (Type w) J K).obj P.carrier ⟶
      (f.sheafPullback (Type w) J K).obj P.carrier :=
  prod.map
      ((Functor.sheafPullback.compSheafComposeIso f
        (CategoryTheory.forget GrpCat.{w}) J K).app G).hom (𝟙 _) ≫
    (PreservesLimitPair.iso (f.sheafPullback (Type w) J K)
      ((sheafForget J).obj G) P.carrier).inv ≫
    (f.sheafPullback (Type w) J K).map (action P)

set_option backward.privateInPublic true in
private def prodSection (A B : Sheaf K (Type w)) {U : Dᵒᵖ}
    (a : A.obj.obj U) (b : B.obj.obj U) : (A ⨯ B).obj.obj U :=
  (PreservesLimitPair.iso (sheafToPresheaf K (Type w)) A B).inv.app U
    (FunctorToTypes.prodMk a b)

-- Exposing scalar multiplication requires access to its private product-section formula.
set_option backward.privateInPublic true in
/-- The sectionwise scalar multiplication transported by sheaf inverse image. -/
def pullbackSmul (G : Sheaf J GrpCat.{w}) (P : Torsor G) (U : D)
    (g : ((f.sheafPullback GrpCat.{w} J K).obj G).obj.obj (op U))
    (x : ((f.sheafPullback (Type w) J K).obj P.carrier).obj.obj (op U)) :
    ((f.sheafPullback (Type w) J K).obj P.carrier).obj.obj (op U) :=
  (pullbackAction K f G P).hom.app (op U)
    (prodSection K
      ((sheafForget K).obj ((f.sheafPullback GrpCat.{w} J K).obj G))
      ((f.sheafPullback (Type w) J K).obj P.carrier) g x)

/-- The unit of the inverse-image group acts trivially on the inverse-image carrier. -/
theorem pullback_one_smul (G : Sheaf J GrpCat.{w}) (P : Torsor G) (U : D)
    (x : ((f.sheafPullback (Type w) J K).obj P.carrier).obj.obj (op U)) :
    pullbackSmul K f G P U 1 x = x := sorry

/-- The transported scalar multiplication respects multiplication of group sections. -/
theorem pullback_mul_smul (G : Sheaf J GrpCat.{w}) (P : Torsor G) (U : D)
    (g h : ((f.sheafPullback GrpCat.{w} J K).obj G).obj.obj (op U))
    (x : ((f.sheafPullback (Type w) J K).obj P.carrier).obj.obj (op U)) :
    pullbackSmul K f G P U (g * h) x =
      pullbackSmul K f G P U g (pullbackSmul K f G P U h x) := sorry

/-- The explicit group action on the sections of the inverse-image carrier. -/
@[implicit_reducible]
def pullbackMulAction (G : Sheaf J GrpCat.{w}) (P : Torsor G) (U : D) :
    MulAction (((f.sheafPullback GrpCat.{w} J K).obj G).obj.obj (op U))
      (((f.sheafPullback (Type w) J K).obj P.carrier).obj.obj (op U)) where
  smul := pullbackSmul K f G P U
  one_smul := pullback_one_smul K f G P U
  mul_smul := pullback_mul_smul K f G P U

/-- Restriction of inverse-image sections commutes with the transported action. -/
theorem pullback_act_naturality (G : Sheaf J GrpCat.{w}) (P : Torsor G)
    {U V : D} (h : V ⟶ U)
    (g : ((f.sheafPullback GrpCat.{w} J K).obj G).obj.obj (op U))
    (x : ((f.sheafPullback (Type w) J K).obj P.carrier).obj.obj (op U)) :
    ((f.sheafPullback (Type w) J K).obj P.carrier).obj.map h.op
        ((pullbackMulAction K f G P U).smul g x) =
      (pullbackMulAction K f G P V).smul
        (((f.sheafPullback GrpCat.{w} J K).obj G).obj.map h.op g)
        (((f.sheafPullback (Type w) J K).obj P.carrier).obj.map h.op x) := sorry

/-- The transported action is pretransitive on sections over every object. -/
theorem pullback_isPretransitive (G : Sheaf J GrpCat.{w}) (P : Torsor G) (U : D) :
    @MulAction.IsPretransitive
      (((f.sheafPullback GrpCat.{w} J K).obj G).obj.obj (op U))
      (((f.sheafPullback (Type w) J K).obj P.carrier).obj.obj (op U))
      (pullbackMulAction K f G P U).toSMul := sorry

/-- The transported action is free on sections over every object. -/
theorem pullback_isCancelSMul (G : Sheaf J GrpCat.{w}) (P : Torsor G) (U : D) :
    @IsCancelSMul
      (((f.sheafPullback GrpCat.{w} J K).obj G).obj.obj (op U))
      (((f.sheafPullback (Type w) J K).obj P.carrier).obj.obj (op U))
      (pullbackMulAction K f G P U).toSMul := sorry

include hLeftExact in
/-- The inverse image of the carrier of a torsor is locally nonempty. -/
theorem pullback_locallyNonempty (G : Sheaf J GrpCat.{w}) (P : Torsor G) (U : D) :
    ∃ S : Sieve U, S ∈ K U ∧
      ∀ ⦃V : D⦄ (h : V ⟶ U), S h →
        Nonempty (((f.sheafPullback (Type w) J K).obj P.carrier).obj.obj (op V)) := sorry

/-- Inverse image of a torsor under a continuous functor with left exact inverse image. -/
def pullback (G : Sheaf J GrpCat.{w}) (P : Torsor G) :
    Torsor ((f.sheafPullback GrpCat.{w} J K).obj G) where
  carrier := (f.sheafPullback (Type w) J K).obj P.carrier
  mulAction := pullbackMulAction K f G P
  act_naturality := pullback_act_naturality K f G P
  isPretransitive := pullback_isPretransitive K f G P
  isCancelSMul := pullback_isCancelSMul K f G P
  locallyNonempty := pullback_locallyNonempty K f G P

/-- The carrier of the inverse-image torsor is the inverse image of its carrier. -/
theorem pullback_carrier (G : Sheaf J GrpCat.{w}) (P : Torsor G) :
    (pullback K f G P).carrier = (f.sheafPullback (Type w) J K).obj P.carrier := rfl

/-- Inverse image of an equivariant sheaf morphism is equivariant for the transported actions. -/
theorem pullback_map_comm {G : Sheaf J GrpCat.{w}} {P Q : Torsor G}
    (h : Torsor.Hom P Q) (U : D)
    (g : ((f.sheafPullback GrpCat.{w} J K).obj G).obj.obj (op U))
    (x : (pullback K f G P).Sections U) :
    ((f.sheafPullback (Type w) J K).map h.hom).hom.app (op U)
        (((pullback K f G P).mulAction U).smul g x) =
      ((pullback K f G Q).mulAction U).smul g
        (((f.sheafPullback (Type w) J K).map h.hom).hom.app (op U) x) := sorry

/-- Inverse image of an equivariant morphism of torsors. -/
def pullbackMap {G : Sheaf J GrpCat.{w}} {P Q : Torsor G} (h : Torsor.Hom P Q) :
    Torsor.Hom (pullback K f G P) (pullback K f G Q) where
  hom := (f.sheafPullback (Type w) J K).map h.hom
  comm := pullback_map_comm K f h

/-- Isomorphic torsors have equal inverse-image isomorphism classes. -/
theorem pullbackIsoClasses_sound (G : Sheaf J GrpCat.{w}) (P Q : Torsor G)
    (h : (Torsor.isomorphicSetoid G).r P Q) :
    (_root_.Quotient.mk'' (pullback K f G P) :
      Torsor.IsoClasses ((f.sheafPullback GrpCat.{w} J K).obj G)) =
      _root_.Quotient.mk'' (pullback K f G Q) := sorry

/-- The map on torsor isomorphism classes induced by sheaf inverse image. -/
def pullbackIsoClasses (G : Sheaf J GrpCat.{w}) :
    Torsor.IsoClasses G → Torsor.IsoClasses ((f.sheafPullback GrpCat.{w} J K).obj G) :=
  _root_.Quotient.lift (fun P ↦ _root_.Quotient.mk'' (pullback K f G P))
    (pullbackIsoClasses_sound K f G)

/-- The inverse-image map on isomorphism classes sends a representative to its inverse image. -/
theorem pullbackIsoClasses_mk (G : Sheaf J GrpCat.{w}) (P : Torsor G) :
    pullbackIsoClasses K f G (_root_.Quotient.mk'' P) = _root_.Quotient.mk'' (pullback K f G P) := rfl

end CategoryTheory.Sheaf.Torsor
