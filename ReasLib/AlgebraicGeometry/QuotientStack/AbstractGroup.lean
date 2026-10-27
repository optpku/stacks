/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Sites.Continuous
public import ReasLib.AlgebraicGeometry.ConstantGroup
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Big
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Basic
public import ReasLib.CategoryTheory.Sites.Torsor.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SmallSheaf
public import ReasLib.AlgebraicGeometry.GroupScheme.RepresentableTorsor

/-!
# Quotient stack of an algebraic space by an abstract group

This module records the stack in groupoids `[[X/G]]` attached to an algebraic
space `X` over `S` equipped with a homomorphism `G →* Aut X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace (toSmallSheaf)

noncomputable section

universe u

namespace AlgebraicGeometry.QuotientStack.AbstractGroup

/-- The functor of locally constant `G`-valued maps is an fppf sheaf. -/
theorem constantGroupSheaf_isSheaf (U : Scheme.{u}) (G : Type u) [Group G] :
    Presheaf.IsSheaf (Scheme.fppfTopology.over U)
      (ConstantGroup.points U (GrpCat.of G)) :=
  (Presheaf.isSheaf_of_iso_iff (ConstantGroup.baseChangePointsIso U (GrpCat.of G))).mp
    (GroupScheme.representableGroup_isSheaf .fppf
      (ConstantGroup.baseChange U (GrpCat.of G)))

/-- The constant sheaf of groups `underline(G)` on `(Sch/U)_fppf`. -/
def constantGroupSheaf (U : Scheme.{u}) (G : Type u) [Group G] :
    Sheaf (Scheme.fppfTopology.over U) GrpCat.{u} where
  obj := ConstantGroup.points U (GrpCat.of G)
  property := constantGroupSheaf_isSheaf U G

/-- The underlying group-valued presheaf of `constantGroupSheaf` is
`ConstantGroup.points`. -/
theorem constantGroupSheaf_obj (U : Scheme.{u}) (G : Type u) [Group G] :
    (constantGroupSheaf U G).obj = ConstantGroup.points U (GrpCat.of G) := rfl

/-- Restriction of an fppf sheaf of types from `(Sch/S)_fppf` to `(Sch/U)_fppf`. -/
def restrict {S : Scheme.{u}} (U : Over S) :
    Sheaf (Scheme.fppfTopology.over S) (Type u) ⥤
      Sheaf (Scheme.fppfTopology.over U.left) (Type u) :=
  (Over.map U.hom).sheafPushforwardContinuous (Type u)
    (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over S)

/-- Inverse image of an fppf sheaf of types along a morphism in `Over S`. -/
def inverseImage {S : Scheme.{u}} {U U' : Over S} (f : U ⟶ U') :
    Sheaf (Scheme.fppfTopology.over U'.left) (Type u) ⥤
      Sheaf (Scheme.fppfTopology.over U.left) (Type u) :=
  (Over.map f.left).sheafPushforwardContinuous (Type u)
    (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over U'.left)

/-- Restriction of an fppf sheaf of groups from `(Sch/S)_fppf` to `(Sch/U)_fppf`. -/
def restrictGrp {S : Scheme.{u}} (U : Over S) :
    Sheaf (Scheme.fppfTopology.over S) GrpCat.{u} ⥤
      Sheaf (Scheme.fppfTopology.over U.left) GrpCat.{u} :=
  (Over.map U.hom).sheafPushforwardContinuous GrpCat.{u}
    (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over S)

/-- Inverse image along an identity morphism of `Over S` is the identity functor. -/
def inverseImageId {S : Scheme.{u}} (U : Over S) :
    inverseImage (𝟙 U) ≅ 𝟭 (Sheaf (Scheme.fppfTopology.over U.left) (Type u)) :=
  Functor.sheafPushforwardContinuousId' (Over.mapId U.left) (Type u)
    (Scheme.fppfTopology.over U.left)

/-- Inverse image is contravariant for composition in `Over S`. -/
def inverseImageComp {S : Scheme.{u}} {U U' U'' : Over S} (f : U ⟶ U') (g : U' ⟶ U'') :
    inverseImage g ⋙ inverseImage f ≅ inverseImage (f ≫ g) :=
  Functor.sheafPushforwardContinuousComp' (Over.mapComp f.left g.left).symm (Type u)
    (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over U'.left)
    (Scheme.fppfTopology.over U''.left)

/-- Restricting from `S` to `U'` and then pulling back along `f : U ⟶ U'` is
restriction to `U`. -/
def restrictIso {S : Scheme.{u}} {U U' : Over S} (f : U ⟶ U') :
    restrict U' ⋙ inverseImage f ≅ restrict U :=
  Functor.sheafPushforwardContinuousComp'
    ((Over.mapComp f.left U'.hom).symm ≪≫ Over.mapCongr (f.left ≫ U'.hom) U.hom f.w)
    (Type u) (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over U'.left)
    (Scheme.fppfTopology.over S)

variable {S : Scheme.{u}} {G : Type u} [Group G] {X : AlgebraicSpace S}

/-- The automorphism `ρ g` of `X`, as an automorphism of the fppf sheaf of points. -/
def autSheaf (ρ : G →* Aut X) (g : G) : toSmallSheaf X ⟶ toSmallSheaf X :=
  Sheaf.homEquiv.symm ((ρ g).hom : (toSmallSheaf X).obj ⟶ (toSmallSheaf X).obj)

/-- The constant section of `underline(G)` with value `g`. -/
def constSection (U : Scheme.{u}) (G : Type u) [Group G] (V : Over U) (g : G) :
    (constantGroupSheaf U G).obj.obj (op V) :=
  LocallyConstant.const V.left g

/-- The action of a group element on a section of an `underline(G)`-torsor. -/
def torsorAct {U : Scheme.{u}} {G : Type u} [Group G]
    (P : Sheaf.Torsor (constantGroupSheaf U G)) (V : (Over U)ᵒᵖ) (g : G)
    (x : P.carrier.obj.obj V) : P.carrier.obj.obj V :=
  (P.mulAction V.unop).toSMul.smul (constSection U G V.unop g) x

/-- Naturality of translation by a constant section of `underline(G)`. -/
theorem torsorAut_naturality {U : Scheme.{u}} {G : Type u} [Group G]
    (P : Sheaf.Torsor (constantGroupSheaf U G)) (g : G) {V W : (Over U)ᵒᵖ} (f : V ⟶ W) :
    P.carrier.obj.map f ≫ TypeCat.ofHom (torsorAct P W g) =
      TypeCat.ofHom (torsorAct P V g) ≫ P.carrier.obj.map f := by
  ext x
  have hconst : (constantGroupSheaf U G).obj.map f (constSection U G V.unop g) =
      constSection U G W.unop g := by
    apply LocallyConstant.ext
    intro y
    rfl
  change torsorAct P W g (P.carrier.obj.map f x) =
    P.carrier.obj.map f (torsorAct P V g x)
  have h := P.act_naturality f.unop (constSection U G V.unop g) x
  change P.carrier.obj.map f (torsorAct P V g x) =
    (P.mulAction W.unop).smul
      ((constantGroupSheaf U G).obj.map f (constSection U G V.unop g))
      (P.carrier.obj.map f x) at h
  rw [hconst] at h
  exact h.symm

/-- Translation by `g` on the underlying sheaf of an `underline(G)`-torsor. -/
def torsorAut {U : Scheme.{u}} {G : Type u} [Group G]
    (P : Sheaf.Torsor (constantGroupSheaf U G)) (g : G) :
    P.carrier ⟶ P.carrier :=
  Sheaf.homEquiv.symm
    { app := fun V ↦ TypeCat.ofHom (torsorAct P V g)
      naturality := fun _ _ f ↦ torsorAut_naturality P g f }

/-- A sheaf map `φ : P ⟶ X|_U` is `G`-equivariant for the action `ρ`. -/
def IsEquivariant (ρ : G →* Aut X) {U : Over S}
    {P : Sheaf.Torsor (constantGroupSheaf U.left G)}
    (φ : P.carrier ⟶ (restrict U).obj (toSmallSheaf X)) : Prop :=
  ∀ g : G, torsorAut P g ≫ φ = φ ≫ (restrict U).map (autSheaf ρ g)

/-- Equivariance is objectwise intertwining of the `G`-actions. -/
theorem IsEquivariant_iff (ρ : G →* Aut X) {U : Over S}
    {P : Sheaf.Torsor (constantGroupSheaf U.left G)}
    (φ : P.carrier ⟶ (restrict U).obj (toSmallSheaf X)) :
    IsEquivariant ρ φ ↔
      ∀ (V : Over U.left) (g : G) (x : P.carrier.obj.obj (op V)),
        φ.hom.app (op V) (torsorAct P (op V) g x) =
          ((restrict U).map (autSheaf ρ g)).hom.app (op V) (φ.hom.app (op V) x) := by
  constructor
  · intro h V g x
    exact congrArg (fun k ↦ k.hom.app (op V) x) (h g)
  · intro h g
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    ext x
    exact h V.unop g x

/-- An object of `[[X/G]]`: a scheme `U` over `S`, an `underline(G)`-torsor on
`(Sch/U)_fppf`, and a `G`-equivariant map to `X`. -/
structure ObjData (ρ : G →* Aut X) where
  /-- The underlying scheme over `S`. -/
  U : Over S
  /-- The `underline(G)`-torsor on `(Sch/U)_fppf`. -/
  P : Sheaf.Torsor (constantGroupSheaf U.left G)
  /-- The `G`-equivariant sheaf map `P ⟶ X|_U`. -/
  φ : P.carrier ⟶ (restrict U).obj (toSmallSheaf X)
  /-- The map `φ` intertwines the `G`-actions. -/
  equivariant : IsEquivariant ρ φ

/-- A morphism of `underline(G)`-torsors over a map of schemes is `G`-equivariant. -/
def IsEquivariantIso {U U' : Over S}
    {P : Sheaf.Torsor (constantGroupSheaf U.left G)}
    {P' : Sheaf.Torsor (constantGroupSheaf U'.left G)} (f : U ⟶ U')
    (g : P.carrier ≅ (inverseImage f).obj P'.carrier) : Prop :=
  ∀ γ : G, torsorAut P γ ≫ g.hom = g.hom ≫ (inverseImage f).map (torsorAut P' γ)

/-- The comparison `φ' ∘ g` after transporting `φ'` along `f`. -/
def triangleMap {ρ : G →* Aut X} {ξ ξ' : ObjData ρ} (f : ξ.U ⟶ ξ'.U)
    (g : ξ.P.carrier ≅ (inverseImage f).obj ξ'.P.carrier) :
    ξ.P.carrier ⟶ (restrict ξ.U).obj (toSmallSheaf X) :=
  g.hom ≫ (inverseImage f).map ξ'.φ ≫ (restrictIso f).hom.app (toSmallSheaf X)

/-- A morphism of `[[X/G]]`: a map of schemes over `S` and a `G`-equivariant
isomorphism of torsors compatible with the maps to `X`. -/
structure Hom {ρ : G →* Aut X} (ξ ξ' : ObjData ρ) where
  /-- The underlying morphism of schemes over `S`. -/
  f : ξ.U ⟶ ξ'.U
  /-- The `G`-equivariant isomorphism `P ≅ f⁻¹ P'`. -/
  g : ξ.P.carrier ≅ (inverseImage f).obj ξ'.P.carrier
  /-- The isomorphism `g` is `G`-equivariant. -/
  equivariant : IsEquivariantIso f g
  /-- The triangle identity `φ = φ' ∘ g`. -/
  comm : ξ.φ = triangleMap f g

/-- The identity comparison of torsors is `G`-equivariant. -/
theorem id_equivariant {ρ : G →* Aut X} (ξ : ObjData ρ) :
    IsEquivariantIso (𝟙 ξ.U) ((inverseImageId ξ.U).symm.app ξ.P.carrier) := by
  intro g
  exact (inverseImageId ξ.U).inv.naturality (torsorAut ξ.P g)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The identity comparison satisfies the triangle identity. -/
theorem id_comm {ρ : G →* Aut X} (ξ : ObjData ρ) :
    ξ.φ = triangleMap (𝟙 ξ.U) ((inverseImageId ξ.U).symm.app ξ.P.carrier) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  ext x
  simp only [restrict, Functor.sheafPushforwardContinuous, Functor.whiskeringLeft, ObjectProperty.lift,
    Functor.comp_obj, ObjectProperty.ι_obj, Functor.comp_map, ObjectProperty.ι_map, Functor.op_obj,
    TypeCat.Fun.toFun_apply, triangleMap, inverseImage, Over.id_left, inverseImageId,
    Functor.sheafPushforwardContinuousId', Functor.sheafPushforwardContinuousIso,
    Functor.sheafPushforwardContinuousNatTrans, Over.mapId, Functor.id_obj, Over.map_obj_left, Iso.trans_symm,
    Iso.symm_mk, NatIso.trans_app, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, restrictIso,
    Functor.sheafPushforwardContinuousComp', Over.mapComp, Over.mapCongr, Iso.symm_self_id, Iso.refl_inv, Iso.refl_hom,
    NatTrans.op_id, NatTrans.comp_app, Category.assoc, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.homMk_hom, op_unop, Functor.sheafPushforwardContinuousId_inv_app_hom_app, Functor.whiskerRight_app,
    NatTrans.op_app, NatIso.ofComponents_hom_app, Functor.whiskerLeft_app,
    Functor.sheafPushforwardContinuousComp_hom_app_hom_app, NatTrans.id_app, Category.id_comp,
    NatTrans.naturality_assoc, Functor.op_map, Quiver.Hom.unop_op, ← Functor.map_comp, comp_apply]
  symm
  calc
    _ = X.toSmallSheaf.obj.map (𝟙 ((Over.map ξ.U.hom).op.obj V))
        (ξ.φ.hom.app V x) := by
      congr 2
    _ = _ := X.toSmallSheaf.obj.map_id_apply _ _

/-- Identity morphisms of `[[X/G]]` are identity on the underlying scheme and
the identity comparison of torsors. -/
def idHom {ρ : G →* Aut X} (ξ : ObjData ρ) : Hom ξ ξ where
  f := 𝟙 ξ.U
  g := (inverseImageId ξ.U).symm.app ξ.P.carrier
  equivariant := id_equivariant ξ
  comm := id_comm ξ

/-- The composite isomorphism of torsors along a composite of scheme maps. -/
def compIso {ρ : G →* Aut X} {ξ ξ' ξ'' : ObjData ρ} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    ξ.P.carrier ≅ (inverseImage (α.f ≫ β.f)).obj ξ''.P.carrier :=
  α.g ≪≫ (inverseImage α.f).mapIso β.g ≪≫
    (inverseImageComp α.f β.f).app ξ''.P.carrier

/-- The composite isomorphism of torsors is `G`-equivariant. -/
theorem comp_equivariant {ρ : G →* Aut X} {ξ ξ' ξ'' : ObjData ρ} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    IsEquivariantIso (α.f ≫ β.f) (compIso α β) := by
  intro g
  change torsorAut ξ.P g ≫
      ((α.g.hom ≫ (inverseImage α.f).map β.g.hom) ≫
        (inverseImageComp α.f β.f).hom.app ξ''.P.carrier) =
    ((α.g.hom ≫ (inverseImage α.f).map β.g.hom) ≫
        (inverseImageComp α.f β.f).hom.app ξ''.P.carrier) ≫
      (inverseImage (α.f ≫ β.f)).map (torsorAut ξ''.P g)
  have hβ := congrArg ((inverseImage α.f).map) (β.equivariant g)
  simp only [Functor.map_comp] at hβ
  have hc := (inverseImageComp α.f β.f).hom.naturality (torsorAut ξ''.P g)
  change (inverseImage α.f).map ((inverseImage β.f).map (torsorAut ξ''.P g)) ≫
      (inverseImageComp α.f β.f).hom.app ξ''.P.carrier =
    (inverseImageComp α.f β.f).hom.app ξ''.P.carrier ≫
      (inverseImage (α.f ≫ β.f)).map (torsorAut ξ''.P g) at hc
  calc
    _ = ((torsorAut ξ.P g ≫ α.g.hom) ≫ (inverseImage α.f).map β.g.hom) ≫
        (inverseImageComp α.f β.f).hom.app ξ''.P.carrier := by
      simp only [Category.assoc]
    _ = (α.g.hom ≫ ((inverseImage α.f).map (torsorAut ξ'.P g) ≫
        (inverseImage α.f).map β.g.hom)) ≫
        (inverseImageComp α.f β.f).hom.app ξ''.P.carrier := by
      rw [α.equivariant g]
      simp only [Category.assoc]
    _ = (α.g.hom ≫ ((inverseImage α.f).map β.g.hom ≫
        (inverseImage α.f).map ((inverseImage β.f).map (torsorAut ξ''.P g)))) ≫
        (inverseImageComp α.f β.f).hom.app ξ''.P.carrier := by rw [hβ]
    _ = _ := by
      simp only [Category.assoc]
      rw [hc]
      rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The composite morphism satisfies the triangle identity. -/
theorem comp_comm {ρ : G →* Aut X} {ξ ξ' ξ'' : ObjData ρ} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    ξ.φ = triangleMap (α.f ≫ β.f) (compIso α β) := by
  have hr :
      (inverseImage α.f).map ((restrictIso β.f).hom.app X.toSmallSheaf) ≫
          (restrictIso α.f).hom.app X.toSmallSheaf =
        (inverseImageComp α.f β.f).hom.app ((restrict ξ''.U).obj X.toSmallSheaf) ≫
          (restrictIso (α.f ≫ β.f)).hom.app X.toSmallSheaf := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    ext x
    simp only [restrict, Functor.sheafPushforwardContinuous, Functor.whiskeringLeft, ObjectProperty.lift,
      Functor.comp_obj, ObjectProperty.ι_obj, Functor.comp_map, ObjectProperty.ι_map, Functor.op_obj, inverseImage,
      restrictIso, Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousIso,
      Functor.sheafPushforwardContinuousNatTrans, Over.mapComp, Over.map_obj_left, Over.mapCongr, Iso.trans_inv,
      Iso.symm_inv, NatTrans.op_comp, Functor.whiskerRight_comp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      ObjectProperty.FullSubcategory.comp_hom, Functor.whiskerLeft_comp, ObjectProperty.homMk_hom, Category.assoc,
      Functor.whiskerLeft_app, Functor.sheafPushforwardContinuousComp_hom_app_hom_app, Functor.whiskerRight_app,
      NatTrans.op_app, NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app, ← Functor.map_comp, ← op_comp,
      Category.id_comp, TypeCat.Fun.toFun_apply, Over.comp_left, inverseImageComp, Functor.op_map, Quiver.Hom.unop_op]
    congr 1
  rw [α.comm]
  dsimp only [triangleMap]
  rw [β.comm]
  dsimp only [triangleMap]
  simp only [CategoryTheory.Functor.map_comp, compIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Category.assoc]
  rw [hr]
  have hc := (inverseImageComp α.f β.f).hom.naturality ξ''.φ
  change (inverseImage α.f).map ((inverseImage β.f).map ξ''.φ) ≫
      (inverseImageComp α.f β.f).hom.app ((restrict ξ''.U).obj X.toSmallSheaf) =
    (inverseImageComp α.f β.f).hom.app ξ''.P.carrier ≫
      (inverseImage (α.f ≫ β.f)).map ξ''.φ at hc
  rw [← Category.assoc ((inverseImage α.f).map ((inverseImage β.f).map ξ''.φ)), hc]
  simp only [Category.assoc]

/-- Composition of morphisms of `[[X/G]]`. -/
def compHom {ρ : G →* Aut X} {ξ ξ' ξ'' : ObjData ρ} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    Hom ξ ξ'' where
  f := α.f ≫ β.f
  g := compIso α β
  equivariant := comp_equivariant α β
  comm := comp_comm α β

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- Compare torsor isomorphisms after transporting along equality of the base maps.
private theorem hom_ext {ρ : G →* Aut X} {ξ ξ' : ObjData ρ} {α β : Hom ξ ξ'}
    (hf : α.f = β.f)
    (hg : ∀ V : Over ξ.U.left,
      α.g.hom.hom.app (op V) ≫ ξ'.P.carrier.obj.map
        ((Over.mapCongr α.f.left β.f.left (congrArg Over.Hom.left hf)).inv.app V).op =
      β.g.hom.hom.app (op V)) : α = β := by
  rcases α with ⟨f, g, h, w⟩
  rcases β with ⟨f', g', h', w'⟩
  dsimp only at hf
  cases hf
  have hg' : g = g' := by
    apply Iso.ext
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    have h := hg V.unop
    change g.hom.hom.app V ≫ ξ'.P.carrier.obj.map (𝟙 _) = g'.hom.hom.app V at h
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at h
    exact h
  cases hg'
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Left identity law for morphisms of `[[X/G]]`. -/
theorem idHom_comp {ρ : G →* Aut X} {ξ ξ' : ObjData ρ} (α : Hom ξ ξ') :
    compHom (idHom ξ) α = α := by
  apply hom_ext (α := compHom (idHom ξ) α) (β := α) (Category.id_comp α.f)
  intro V
  ext x
  simp only [idHom, inverseImage, Over.id_left, Functor.sheafPushforwardContinuous, Functor.whiskeringLeft,
    ObjectProperty.lift, Functor.comp_obj, ObjectProperty.ι_obj, Functor.comp_map, ObjectProperty.ι_map, inverseImageId,
    Over.mapId, Functor.id_obj, Over.map_obj_left, Functor.sheafPushforwardContinuousId',
    Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans, Iso.trans_symm, Iso.symm_mk,
    NatIso.trans_app, compHom, compIso, Over.comp_left, inverseImageComp, Over.mapComp,
    Functor.sheafPushforwardContinuousComp', Iso.symm_inv, Iso.symm_hom, Functor.op_obj, Iso.trans_assoc, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
    NatTrans.comp_app, Functor.sheafPushforwardContinuousId_inv_app_hom_app, Functor.whiskerRight_app, NatTrans.op_app,
    NatIso.ofComponents_hom_app, Functor.whiskerLeft_app, Functor.sheafPushforwardContinuousComp_hom_app_hom_app,
    Category.id_comp, NatTrans.naturality_assoc, Functor.op_map, Quiver.Hom.unop_op, Over.mapCongr,
    NatIso.ofComponents_inv_app, Category.assoc, TypeCat.Fun.toFun_apply, comp_apply]
  simp only [← CategoryTheory.Functor.map_comp_apply, ← op_comp]
  calc
    _ = ξ'.P.carrier.obj.map (𝟙 (op ((Over.map α.f.left).obj V)))
        (α.g.hom.hom.app (op V) x) := by
      congr 2
    _ = _ := ξ'.P.carrier.obj.map_id_apply _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Right identity law for morphisms of `[[X/G]]`. -/
theorem compHom_id {ρ : G →* Aut X} {ξ ξ' : ObjData ρ} (α : Hom ξ ξ') :
    compHom α (idHom ξ') = α := by
  apply hom_ext (α := compHom α (idHom ξ')) (β := α) (Category.comp_id α.f)
  intro V
  ext x
  simp only [idHom, inverseImage, Over.id_left, Functor.sheafPushforwardContinuous, Functor.whiskeringLeft,
    ObjectProperty.lift, Functor.comp_obj, ObjectProperty.ι_obj, Functor.comp_map, ObjectProperty.ι_map, inverseImageId,
    Over.mapId, Functor.id_obj, Over.map_obj_left, Functor.sheafPushforwardContinuousId',
    Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans, Iso.trans_symm, Iso.symm_mk,
    NatIso.trans_app, compHom, compIso, Over.comp_left, inverseImageComp, Over.mapComp,
    Functor.sheafPushforwardContinuousComp', Iso.symm_inv, Iso.symm_hom, Functor.op_obj, Functor.mapIso_trans,
    Iso.trans_assoc, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.homMk_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.sheafPushforwardContinuousId_inv_app_hom_app, Functor.whiskerRight_app, NatTrans.op_app,
    NatIso.ofComponents_hom_app, Functor.sheafPushforwardContinuousComp_hom_app_hom_app, Category.id_comp,
    Over.mapCongr, NatIso.ofComponents_inv_app, Category.assoc, TypeCat.Fun.toFun_apply, comp_apply]
  simp only [← CategoryTheory.Functor.map_comp_apply, ← op_comp]
  calc
    _ = ξ'.P.carrier.obj.map (𝟙 (op ((Over.map α.f.left).obj V)))
        (α.g.hom.hom.app (op V) x) := by
      congr 2
    _ = _ := ξ'.P.carrier.obj.map_id_apply _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Associativity of composition of morphisms of `[[X/G]]`. -/
theorem assocHom {ρ : G →* Aut X} {ξ₁ ξ₂ ξ₃ ξ₄ : ObjData ρ}
    (α : Hom ξ₁ ξ₂) (β : Hom ξ₂ ξ₃) (γ : Hom ξ₃ ξ₄) :
    compHom (compHom α β) γ = compHom α (compHom β γ) := by
  apply hom_ext (α := compHom (compHom α β) γ)
    (β := compHom α (compHom β γ)) (Category.assoc α.f β.f γ.f)
  intro V
  ext x
  simp only [compHom, compIso, inverseImage, Functor.sheafPushforwardContinuous, Functor.whiskeringLeft,
    ObjectProperty.lift, Functor.comp_obj, ObjectProperty.ι_obj, Functor.comp_map, ObjectProperty.ι_map, Over.comp_left,
    inverseImageComp, Over.mapComp, Over.map_obj_left, Functor.sheafPushforwardContinuousComp',
    Functor.sheafPushforwardContinuousIso, Iso.symm_inv, Functor.sheafPushforwardContinuousNatTrans, Iso.symm_hom,
    NatIso.trans_app, Functor.op_obj, Iso.trans_assoc, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.sheafPushforwardContinuousComp_hom_app_hom_app, Functor.whiskerRight_app, NatTrans.op_app,
    NatIso.ofComponents_hom_app, Category.id_comp, NatTrans.naturality_assoc, Functor.op_map, Quiver.Hom.unop_op,
    Over.mapCongr, NatIso.ofComponents_inv_app, Category.assoc, TypeCat.Fun.toFun_apply, comp_apply,
    Functor.mapIso_trans, Functor.whiskerLeft_twice, Functor.associator_inv_app, Functor.associator_hom_app]
  simp only [← CategoryTheory.Functor.map_comp_apply, ← op_comp]
  congr 2

/-- The category of constant-group torsors equipped with an equivariant map to an algebraic space. -/
def category (ρ : G →* Aut X) : Cat.{u + 1, u + 1} :=
  ⟨ObjData ρ, {
    Hom := fun ξ ξ' ↦ Hom ξ ξ'
    id := idHom
    comp := compHom
    id_comp := idHom_comp
    comp_id := compHom_id
    assoc := assocHom
  }⟩

/-- The carrier of the category of constant-group torsors with an equivariant map. -/
abbrev Obj (ρ : G →* Aut X) : Type (u + 1) := category ρ

/-- Assemble an object of `[[X/G]]` from a torsor and an equivariant map to `X`. -/
def ofTorsor (ρ : G →* Aut X) {U : Over S}
    (P : Sheaf.Torsor (constantGroupSheaf U.left G))
    (φ : P.carrier ⟶ (restrict U).obj (toSmallSheaf X)) (h : IsEquivariant ρ φ) :
    Obj ρ where
  U := U
  P := P
  φ := φ
  equivariant := h

/-- The constructor of `Obj` stores the supplied scheme, torsor, map, and
equivariance witness. -/
theorem ofTorsor_spec (ρ : G →* Aut X) {U : Over S}
    (P : Sheaf.Torsor (constantGroupSheaf U.left G))
    (φ : P.carrier ⟶ (restrict U).obj (toSmallSheaf X)) (h : IsEquivariant ρ φ) :
    (ofTorsor ρ P φ h).U = U ∧ (ofTorsor ρ P φ h).P = P ∧
      (ofTorsor ρ P φ h).φ = φ ∧ (ofTorsor ρ P φ h).equivariant = h := ⟨rfl, rfl, rfl, rfl⟩

/-- Assemble a morphism of `[[X/G]]` from a scheme map and an equivariant
isomorphism of torsors. -/
def ofIso {ρ : G →* Aut X} {ξ ξ' : Obj ρ} (f : ξ.U ⟶ ξ'.U)
    (g : ξ.P.carrier ≅ (inverseImage f).obj ξ'.P.carrier)
    (h : IsEquivariantIso f g) (w : ξ.φ = triangleMap f g) :
    Hom ξ ξ' where
  f := f
  g := g
  equivariant := h
  comm := w

/-- The constructor of `Hom` stores the supplied scheme map, isomorphism, and
compatibilities. -/
theorem ofIso_spec {ρ : G →* Aut X} {ξ ξ' : Obj ρ} (f : ξ.U ⟶ ξ'.U)
    (g : ξ.P.carrier ≅ (inverseImage f).obj ξ'.P.carrier)
    (h : IsEquivariantIso f g) (w : ξ.φ = triangleMap f g) :
    (ofIso f g h w).f = f ∧ (ofIso f g h w).g = g ∧
      (ofIso f g h w).equivariant = h ∧ (ofIso f g h w).comm = w := ⟨rfl, rfl, rfl, rfl⟩

/-- The forgetful functor sends identity morphisms to identity morphisms. -/
theorem forget_map_id {ρ : G →* Aut X} (ξ : Obj ρ) : (idHom ξ).f = 𝟙 ξ.U := rfl

/-- The forgetful functor preserves composition. -/
theorem forget_map_comp {ρ : G →* Aut X} {ξ ξ' ξ'' : Obj ρ} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    (compHom α β).f = α.f ≫ β.f := rfl

/-- The forgetful functor `[[X/G]] ⟶ (Sch/S)_fppf`. -/
def forget (ρ : G →* Aut X) : Obj ρ ⥤ Over S where
  obj ξ := ξ.U
  map α := α.f
  map_id := forget_map_id
  map_comp := forget_map_comp

/-- The forgetful functor sends `(U, P, φ)` to `U`. -/
theorem forget_obj {ρ : G →* Aut X} (ξ : Obj ρ) : (forget ρ).obj ξ = ξ.U := rfl

/-- The forgetful functor sends a morphism `(f, g)` to `f`. -/
theorem forget_map {ρ : G →* Aut X} {ξ ξ' : Obj ρ} (α : Hom ξ ξ') : (forget ρ).map α = α.f := rfl

/-- The forgetful functor `[[X/G]] ⟶ (Sch/S)_fppf` is a stack in groupoids. -/
instance instIsStackInGroupoids (ρ : G →* Aut X) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (forget ρ) := sorry

/-- The stack in groupoids `[[X/G]]` over `(Sch/S)_fppf`. -/
def stack (ρ : G →* Aut X) : StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  StackOver.Groupoids.ofProjection (Scheme.fppfTopology.over S) (forget ρ)

/-- The projection of `stack` is the forgetful functor to `(Sch/S)_fppf`. -/
theorem stack_p (ρ : G →* Aut X) : (stack ρ).p = forget ρ := rfl

end AlgebraicGeometry.QuotientStack.AbstractGroup
