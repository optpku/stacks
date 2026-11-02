/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SmallSheaf
public import ReasLib.AlgebraicGeometry.QuotientStack.Inertia.Coproduct
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Definition
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Groupoids.Objects
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification
public import ReasLib.CategoryTheory.Inertia.Relative

/-!
# Fixed-locus quotients and inertia

The fixed-locus inclusion and torsor translation define a cartesian comparison from the
sigma-category of fixed-locus quotients to the inertia of the original quotient stack.
-/

@[expose] public section

open CategoryTheory
open Opposite
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.QuotientStack.AbstractGroup
open AlgebraicGeometry.Scheme.GroupAction.FixedLocus
open scoped CategoryTheory.BasedFunctor

noncomputable section

universe u

namespace AlgebraicGeometry.QuotientStack.InertiaCoprod

variable {S : Scheme.{u}} {G : Type u} [CommGroup G] {X : Over S}

/-- Translations by mutually inverse constant sections are mutually inverse sheaf maps. -/
private theorem torsorAutIso_laws {U : Scheme.{u}}
    (P : Sheaf.Torsor (constantGroupSheaf U G)) (g : G) :
    torsorAut P g ≫ torsorAut P g⁻¹ = 𝟙 P.carrier ∧
      torsorAut P g⁻¹ ≫ torsorAut P g = 𝟙 P.carrier := by
  constructor
  · apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    ext x
    letI := P.mulAction V.unop
    change (constSection U G V.unop g⁻¹) • ((constSection U G V.unop g) • x) = x
    have hinv : constSection U G V.unop g⁻¹ = (constSection U G V.unop g)⁻¹ := rfl
    rw [hinv, inv_smul_smul]
  · apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    ext x
    letI := P.mulAction V.unop
    change (constSection U G V.unop g) • ((constSection U G V.unop g⁻¹) • x) = x
    have hinv : constSection U G V.unop g⁻¹ = (constSection U G V.unop g)⁻¹ := rfl
    rw [hinv, smul_inv_smul]

/-- Translation by a group element is an isomorphism of the underlying torsor sheaf. -/
def torsorAutIso {U : Scheme.{u}} (P : Sheaf.Torsor (constantGroupSheaf U G)) (g : G) :
    P.carrier ≅ P.carrier where
  hom := torsorAut P g
  inv := torsorAut P g⁻¹
  hom_inv_id := by exact (torsorAutIso_laws P g).1
  inv_hom_id := by exact (torsorAutIso_laws P g).2

/-- Postcompose a map to a fixed locus with the sheaf map of its inclusion. -/
def includeφ (ρ : G →* Aut X) (g : G) {U : Over S}
    {P : Sheaf.Torsor (constantGroupSheaf U.left G)}
    (φ : P.carrier ⟶ (restrict U).obj (toSmallSheaf (ofOver (fixedLocus ρ g)))) :
    P.carrier ⟶ (restrict U).obj (toSmallSheaf (ofOver X)) :=
  φ ≫ (restrict U).map
    (Sheaf.homEquiv.symm (yoneda.map (inclusion ρ g)) :
      toSmallSheaf (ofOver (fixedLocus ρ g)) ⟶ toSmallSheaf (ofOver X))

/-- The map induced by a fixed-locus inclusion is given by sheaf-map postcomposition. -/
theorem includeφ_spec (ρ : G →* Aut X) (g : G) {U : Over S}
    {P : Sheaf.Torsor (constantGroupSheaf U.left G)}
    (φ : P.carrier ⟶ (restrict U).obj (toSmallSheaf (ofOver (fixedLocus ρ g)))) :
    includeφ ρ g φ =
      φ ≫ (restrict U).map
        (Sheaf.homEquiv.symm (yoneda.map (inclusion ρ g)) :
          toSmallSheaf (ofOver (fixedLocus ρ g)) ⟶ toSmallSheaf (ofOver X)) :=
  rfl

/-- Postcomposition with the fixed-locus inclusion preserves equivariance. -/
private theorem includeObj_equivariant (ρ : G →* Aut X) (g : G)
    (ξ : Obj (((ofOverFunctor S).mapAut _).comp (residual ρ g))) :
    IsEquivariant (((ofOverFunctor S).mapAut _).comp ρ) (includeφ ρ g ξ.φ) := by
  intro γ
  let i : toSmallSheaf (ofOver (fixedLocus ρ g)) ⟶ toSmallSheaf (ofOver X) :=
    Sheaf.homEquiv.symm (yoneda.map (inclusion ρ g))
  have hi : autSheaf (((ofOverFunctor S).mapAut _).comp (residual ρ g)) γ ≫ i =
      i ≫ autSheaf (((ofOverFunctor S).mapAut _).comp ρ) γ := by
    apply Sheaf.homEquiv.injective
    change yoneda.map (residual ρ g γ).hom ≫ yoneda.map (inclusion ρ g) =
      yoneda.map (inclusion ρ g) ≫ yoneda.map (ρ γ).hom
    rw [← yoneda.map_comp, ← yoneda.map_comp, residual_hom]
  change torsorAut ξ.P γ ≫ (ξ.φ ≫ (restrict ξ.U).map i) =
    (ξ.φ ≫ (restrict ξ.U).map i) ≫
      (restrict ξ.U).map (autSheaf (((ofOverFunctor S).mapAut _).comp ρ) γ)
  calc
    _ = (torsorAut ξ.P γ ≫ ξ.φ) ≫ (restrict ξ.U).map i :=
      (Category.assoc _ _ _).symm
    _ = (ξ.φ ≫ (restrict ξ.U).map
        (autSheaf (((ofOverFunctor S).mapAut _).comp (residual ρ g)) γ)) ≫
          (restrict ξ.U).map i := by rw [ξ.equivariant γ]
    _ = ξ.φ ≫ (restrict ξ.U).map
        (autSheaf (((ofOverFunctor S).mapAut _).comp (residual ρ g)) γ ≫ i) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun f ↦ ξ.φ ≫ f) ((restrict ξ.U).map_comp _ _).symm)
    _ = ξ.φ ≫ (restrict ξ.U).map
        (i ≫ autSheaf (((ofOverFunctor S).mapAut _).comp ρ) γ) :=
      congrArg (fun f ↦ ξ.φ ≫ (restrict ξ.U).map f) hi
    _ = _ := (congrArg (fun f ↦ ξ.φ ≫ f) ((restrict ξ.U).map_comp _ _)).trans
      (Category.assoc _ _ _).symm

/-- A fixed-locus quotient object induces a quotient object with the same test scheme and torsor. -/
def includeObj (ρ : G →* Aut X) (g : G)
    (ξ : Obj (((ofOverFunctor S).mapAut _).comp (residual ρ g))) :
    Obj (((ofOverFunctor S).mapAut _).comp ρ) where
  U := ξ.U
  P := ξ.P
  φ := includeφ ρ g ξ.φ
  equivariant := by exact includeObj_equivariant ρ g ξ

/-- The fixed-locus inclusion retains the test scheme and torsor of a quotient object. -/
theorem includeObj_spec (ρ : G →* Aut X) (g : G)
    (ξ : Obj (((ofOverFunctor S).mapAut _).comp (residual ρ g))) :
    (includeObj ρ g ξ).U = ξ.U ∧ (includeObj ρ g ξ).P = ξ.P :=
  ⟨rfl, rfl⟩

/-- A quotient morphism remains equivariant and satisfies its triangle after a fixed-locus inclusion. -/
private theorem includeMap_laws (ρ : G →* Aut X) (g : G)
    {ξ ξ' : Obj (((ofOverFunctor S).mapAut _).comp (residual ρ g))} (α : ξ ⟶ ξ') :
    IsEquivariantIso α.f α.g ∧
      (includeObj ρ g ξ).φ =
        triangleMap (ξ := includeObj ρ g ξ) (ξ' := includeObj ρ g ξ') α.f α.g := by
  refine ⟨α.equivariant, ?_⟩
  let i : toSmallSheaf (ofOver (fixedLocus ρ g)) ⟶ toSmallSheaf (ofOver X) :=
    Sheaf.homEquiv.symm (yoneda.map (inclusion ρ g))
  change ξ.φ ≫ (restrict ξ.U).map i =
    α.g.hom ≫ (inverseImage α.f).map (ξ'.φ ≫ (restrict ξ'.U).map i) ≫
      (restrictIso α.f).hom.app (toSmallSheaf (ofOver X))
  rw [α.comm]
  dsimp only [triangleMap]
  simp only [Functor.map_comp, Category.assoc]
  exact congrArg (fun f ↦ α.g.hom ≫ (inverseImage α.f).map ξ'.φ ≫ f)
    ((restrictIso α.f).hom.naturality i).symm

/-- Postcompose a fixed-locus quotient morphism with the fixed-locus inclusion. -/
def includeMap (ρ : G →* Aut X) (g : G)
    {ξ ξ' : Obj (((ofOverFunctor S).mapAut _).comp (residual ρ g))} (α : ξ ⟶ ξ') :
    includeObj ρ g ξ ⟶ includeObj ρ g ξ' where
  f := α.f
  g := α.g
  equivariant := by exact (includeMap_laws ρ g α).1
  comm := by exact (includeMap_laws ρ g α).2

/-- The fixed-locus inclusion retains the underlying scheme map of a quotient morphism. -/
theorem includeMap_f (ρ : G →* Aut X) (g : G)
    {ξ ξ' : Obj (((ofOverFunctor S).mapAut _).comp (residual ρ g))} (α : ξ ⟶ ξ') :
    (includeMap ρ g α).f = α.f :=
  rfl

/-- A translation preserving the quotient map satisfies equivariance and the quotient triangle. -/
private theorem mulHom_laws {Y : AlgebraicSpace S} (σ : G →* Aut Y) (ξ : Obj σ)
    (g : G) (h : torsorAut ξ.P g ≫ ξ.φ = ξ.φ) :
    IsEquivariantIso (𝟙 ξ.U)
        (torsorAutIso ξ.P g ≪≫ (inverseImageId ξ.U).symm.app ξ.P.carrier) ∧
      ξ.φ = triangleMap (ξ := ξ) (ξ' := ξ) (𝟙 ξ.U)
        (torsorAutIso ξ.P g ≪≫ (inverseImageId ξ.U).symm.app ξ.P.carrier) := by
  constructor
  · intro γ
    have hcomm : torsorAut ξ.P γ ≫ torsorAut ξ.P g =
        torsorAut ξ.P g ≫ torsorAut ξ.P γ := by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext V
      ext x
      letI := ξ.P.mulAction V.unop
      change (constSection ξ.U.left G V.unop g) •
          ((constSection ξ.U.left G V.unop γ) • x) =
        (constSection ξ.U.left G V.unop γ) •
          ((constSection ξ.U.left G V.unop g) • x)
      rw [← mul_smul, ← mul_smul]
      congr 1
      exact LocallyConstant.ext (fun _ ↦ mul_comm g γ)
    change torsorAut ξ.P γ ≫
        (torsorAut ξ.P g ≫ (inverseImageId ξ.U).inv.app ξ.P.carrier) =
      (torsorAut ξ.P g ≫ (inverseImageId ξ.U).inv.app ξ.P.carrier) ≫
        (inverseImage (𝟙 ξ.U)).map (torsorAut ξ.P γ)
    calc
      _ = (torsorAut ξ.P γ ≫ torsorAut ξ.P g) ≫
          (inverseImageId ξ.U).inv.app ξ.P.carrier := (Category.assoc _ _ _).symm
      _ = (torsorAut ξ.P g ≫ torsorAut ξ.P γ) ≫
          (inverseImageId ξ.U).inv.app ξ.P.carrier :=
        congrArg (fun f ↦ f ≫ (inverseImageId ξ.U).inv.app ξ.P.carrier) hcomm
      _ = torsorAut ξ.P g ≫ ((inverseImageId ξ.U).inv.app ξ.P.carrier ≫
          (inverseImage (𝟙 ξ.U)).map (torsorAut ξ.P γ)) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun f ↦ torsorAut ξ.P g ≫ f)
            ((inverseImageId ξ.U).inv.naturality (torsorAut ξ.P γ)))
      _ = _ := (Category.assoc _ _ _).symm
  · change ξ.φ =
      (torsorAut ξ.P g ≫ (inverseImageId ξ.U).inv.app ξ.P.carrier) ≫
        (inverseImage (𝟙 ξ.U)).map ξ.φ ≫
          (restrictIso (𝟙 ξ.U)).hom.app (toSmallSheaf Y)
    rw [Category.assoc]
    change ξ.φ = torsorAut ξ.P g ≫
      triangleMap (ξ := ξ) (ξ' := ξ) (𝟙 ξ.U)
        ((inverseImageId ξ.U).symm.app ξ.P.carrier)
    rw [← id_comm ξ, h]

/-- A translation preserving the equivariant map defines an endomorphism of the quotient object. -/
def mulHom {Y : AlgebraicSpace S} (σ : G →* Aut Y) (ξ : Obj σ) (g : G)
    (h : torsorAut ξ.P g ≫ ξ.φ = ξ.φ) : Hom ξ ξ where
  f := 𝟙 ξ.U
  g := torsorAutIso ξ.P g ≪≫ (inverseImageId ξ.U).symm.app ξ.P.carrier
  equivariant := by exact (mulHom_laws σ ξ g h).1
  comm := by exact (mulHom_laws σ ξ g h).2

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Quotient arrows are determined by their base map and transported torsor map. -/
private theorem quotientHom_ext {Y : AlgebraicSpace S} {σ : G →* Aut Y}
    {ξ ξ' : Obj σ} {α β : Hom ξ ξ'}
    (hf : α.f = β.f)
    (hg : ∀ V : Over ξ.U.left,
      α.g.hom.hom.app (Opposite.op V) ≫ ξ'.P.carrier.obj.map
        ((Over.mapCongr α.f.left β.f.left (congrArg Over.Hom.left hf)).inv.app V).op =
      β.g.hom.hom.app (Opposite.op V)) : α = β := by
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

/-- Inverse translation preserves a map whenever the original translation preserves it. -/
private theorem mulAut_inverse_fixed {Y : AlgebraicSpace S} (σ : G →* Aut Y)
    (ξ : Obj σ) (g : G) (h : torsorAut ξ.P g ≫ ξ.φ = ξ.φ) :
    torsorAut ξ.P g⁻¹ ≫ ξ.φ = ξ.φ := by
  calc
    torsorAut ξ.P g⁻¹ ≫ ξ.φ =
        torsorAut ξ.P g⁻¹ ≫ (torsorAut ξ.P g ≫ ξ.φ) := by rw [h]
    _ = (torsorAut ξ.P g⁻¹ ≫ torsorAut ξ.P g) ≫ ξ.φ :=
      (Category.assoc _ _ _).symm
    _ = ξ.φ := by rw [(torsorAutIso_laws ξ.P g).2, Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The quotient endomorphisms of mutually inverse preserving translations are mutually inverse. -/
private theorem mulAut_laws {Y : AlgebraicSpace S} (σ : G →* Aut Y) (ξ : Obj σ)
    (g : G) (h : torsorAut ξ.P g ≫ ξ.φ = ξ.φ) :
    mulHom σ ξ g h ≫ mulHom σ ξ g⁻¹ (mulAut_inverse_fixed σ ξ g h) = 𝟙 ξ ∧
      mulHom σ ξ g⁻¹ (mulAut_inverse_fixed σ ξ g h) ≫ mulHom σ ξ g h = 𝟙 ξ := by
  have comp_eq_id (a b : G) (ha : torsorAut ξ.P a ≫ ξ.φ = ξ.φ)
      (hb : torsorAut ξ.P b ≫ ξ.φ = ξ.φ)
      (hc : torsorAut ξ.P a ≫ torsorAut ξ.P b = 𝟙 ξ.P.carrier) :
      mulHom σ ξ a ha ≫ mulHom σ ξ b hb = 𝟙 ξ := by
    change compHom (mulHom σ ξ a ha) (mulHom σ ξ b hb) = idHom ξ
    apply quotientHom_ext (Category.id_comp (𝟙 ξ.U))
    intro V
    ext x
    simp only [mulHom, torsorAutIso, idHom, inverseImage, Over.id_left,
      Functor.sheafPushforwardContinuous, Functor.whiskeringLeft,
      ObjectProperty.lift, Functor.comp_obj, ObjectProperty.ι_obj, Functor.comp_map,
      ObjectProperty.ι_map, inverseImageId,
      Over.mapId, Functor.id_obj, Over.map_obj_left, Functor.sheafPushforwardContinuousId',
      Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans,
      Iso.trans_symm, Iso.symm_mk,
      NatIso.trans_app, compHom, compIso, Over.comp_left, inverseImageComp, Over.mapComp,
      Functor.sheafPushforwardContinuousComp', Iso.symm_inv, Iso.symm_hom, Functor.op_obj,
      Iso.trans_assoc, Iso.trans_hom,
      Iso.app_hom, Functor.mapIso_hom, ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.homMk_hom,
      NatTrans.comp_app, Functor.sheafPushforwardContinuousId_inv_app_hom_app,
      Functor.whiskerRight_app, NatTrans.op_app,
      NatIso.ofComponents_hom_app, Functor.whiskerLeft_app,
      Functor.sheafPushforwardContinuousComp_hom_app_hom_app,
      Category.id_comp, NatTrans.naturality_assoc, Over.mapCongr,
      NatIso.ofComponents_inv_app, Category.assoc, TypeCat.Fun.toFun_apply, comp_apply]
    simp only [← CategoryTheory.Functor.map_comp_apply, ← op_comp]
    have hcx := congrArg (fun f ↦ f.hom.app (op V) x) hc
    change (torsorAut ξ.P b).hom.app (op V)
      ((torsorAut ξ.P a).hom.app (op V) x) = x at hcx
    rw [hcx]
    congr 2
  exact ⟨comp_eq_id g g⁻¹ h (mulAut_inverse_fixed σ ξ g h) (torsorAutIso_laws ξ.P g).1,
    comp_eq_id g⁻¹ g (mulAut_inverse_fixed σ ξ g h) h (torsorAutIso_laws ξ.P g).2⟩

/-- A translation preserving the equivariant map gives an automorphism of a quotient object. -/
def mulAut {Y : AlgebraicSpace S} (σ : G →* Aut Y) (ξ : Obj σ) (g : G)
    (h : torsorAut ξ.P g ≫ ξ.φ = ξ.φ) : Aut ξ where
  hom := mulHom σ ξ g h
  inv := mulHom σ ξ g⁻¹ (by exact mulAut_inverse_fixed σ ξ g h)
  hom_inv_id := by exact (mulAut_laws σ ξ g h).1
  inv_hom_id := by exact (mulAut_laws σ ξ g h).2

/-- Translation by a fixed-locus index preserves the induced map to the acting scheme. -/
private theorem includeObj_fixed (ρ : G →* Aut X) (g : G)
    (ξ : Obj (((ofOverFunctor S).mapAut _).comp (residual ρ g))) :
    torsorAut ξ.P g ≫ (includeObj ρ g ξ).φ = (includeObj ρ g ξ).φ := by
  let i : toSmallSheaf (ofOver (fixedLocus ρ g)) ⟶ toSmallSheaf (ofOver X) :=
    Sheaf.homEquiv.symm (yoneda.map (inclusion ρ g))
  have hi : i ≫ autSheaf (((ofOverFunctor S).mapAut _).comp ρ) g = i := by
    apply Sheaf.homEquiv.injective
    change yoneda.map (inclusion ρ g) ≫ yoneda.map (ρ g).hom =
      yoneda.map (inclusion ρ g)
    rw [← yoneda.map_comp, inclusion_spec]
  exact ((includeObj ρ g ξ).equivariant g).trans
    ((Category.assoc ξ.φ ((restrict ξ.U).map i)
      ((restrict ξ.U).map (autSheaf (((ofOverFunctor S).mapAut _).comp ρ) g))).trans
      ((congrArg (fun f ↦ ξ.φ ≫ f)
        ((restrict ξ.U).map_comp i
          (autSheaf (((ofOverFunctor S).mapAut _).comp ρ) g)).symm).trans
        (congrArg (fun f ↦ ξ.φ ≫ (restrict ξ.U).map f) hi)))

/-- The translation automorphism of an included fixed-locus quotient object is vertical. -/
private theorem toInertiaObj_kernel (ρ : G →* Aut X) (g : G)
    (ξ : Obj (((ofOverFunctor S).mapAut _).comp (residual ρ g)))
    (h : torsorAut ξ.P g ≫ (includeObj ρ g ξ).φ = (includeObj ρ g ξ).φ) :
    (forget (((ofOverFunctor S).mapAut _).comp ρ)).mapAut (includeObj ρ g ξ)
      (mulAut (((ofOverFunctor S).mapAut _).comp ρ) (includeObj ρ g ξ) g h) = 1 := by
  apply Iso.ext
  rfl

/-- A fixed-locus quotient object determines an inertia object by translation by its index. -/
def toInertiaObj (ρ : G →* Aut X) (ξ : CoprodObj ρ) :
    RelativeInertia (forget (((ofOverFunctor S).mapAut _).comp ρ)) :=
  let h : torsorAut ξ.2.P ξ.1 ≫ (includeObj ρ ξ.1 ξ.2).φ =
      (includeObj ρ ξ.1 ξ.2).φ := by exact includeObj_fixed ρ ξ.1 ξ.2
  RelativeInertia.mk (Inertia.mk (includeObj ρ ξ.1 ξ.2)
    (mulAut (((ofOverFunctor S).mapAut _).comp ρ) (includeObj ρ ξ.1 ξ.2) ξ.1 h))
    (by exact toInertiaObj_kernel ρ ξ.1 ξ.2 h)

/-- The inertia comparison retains the test scheme of a summand object. -/
theorem toInertia_idx (ρ : G →* Aut X) (ξ : CoprodObj ρ) :
    (toInertiaObj ρ ξ).obj.U = ξ.2.U :=
  rfl

/-- The inertia comparison's chosen automorphism lies over the identity of the test scheme. -/
theorem toInertia_aut (ρ : G →* Aut X) (ξ : CoprodObj ρ) :
    (toInertiaObj ρ ξ).aut.hom.f = 𝟙 ξ.2.U :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Included quotient morphisms intertwine the translations indexing their common summand. -/
private theorem toInertiaMap_comm (ρ : G →* Aut X) (g : G)
    {ξ ξ' : Obj (((ofOverFunctor S).mapAut _).comp (residual ρ g))} (α : ξ ⟶ ξ') :
    (toInertiaObj ρ (ofSummand ρ g ξ)).aut.hom ≫ includeMap ρ g α =
      includeMap ρ g α ≫ (toInertiaObj ρ (ofSummand ρ g ξ')).aut.hom := by
  change compHom
      (mulHom (((ofOverFunctor S).mapAut _).comp ρ) (includeObj ρ g ξ) g
        (includeObj_fixed ρ g ξ)) (includeMap ρ g α) =
    compHom (includeMap ρ g α)
      (mulHom (((ofOverFunctor S).mapAut _).comp ρ) (includeObj ρ g ξ') g
        (includeObj_fixed ρ g ξ'))
  apply quotientHom_ext
    (α := compHom (mulHom (((ofOverFunctor S).mapAut _).comp ρ) (includeObj ρ g ξ) g
      (includeObj_fixed ρ g ξ)) (includeMap ρ g α))
    (β := compHom (includeMap ρ g α)
      (mulHom (((ofOverFunctor S).mapAut _).comp ρ) (includeObj ρ g ξ') g
        (includeObj_fixed ρ g ξ')))
    ((Category.id_comp α.f).trans (Category.comp_id α.f).symm)
  intro V
  ext x
  simp only [includeMap, includeObj, mulHom, torsorAutIso, inverseImage, Over.id_left,
    Functor.sheafPushforwardContinuous, Functor.whiskeringLeft,
      ObjectProperty.lift, Functor.comp_obj, ObjectProperty.ι_obj, Functor.comp_map,
      ObjectProperty.ι_map, inverseImageId,
      Over.mapId, Functor.id_obj, Over.map_obj_left, Functor.sheafPushforwardContinuousId',
      Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans,
      Iso.trans_symm, Iso.symm_mk,
      NatIso.trans_app, compHom, compIso, Over.comp_left, inverseImageComp, Over.mapComp,
      Functor.sheafPushforwardContinuousComp', Iso.symm_inv, Iso.symm_hom, Functor.op_obj,
      Iso.trans_assoc, Iso.trans_hom,
      Iso.app_hom, Functor.mapIso_hom, ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.homMk_hom,
      NatTrans.comp_app, Functor.sheafPushforwardContinuousId_inv_app_hom_app,
      Functor.whiskerRight_app, NatTrans.op_app,
      NatIso.ofComponents_hom_app, Functor.whiskerLeft_app,
      Functor.sheafPushforwardContinuousComp_hom_app_hom_app,
      Category.id_comp, NatTrans.naturality_assoc, Functor.op_map, Quiver.Hom.unop_op,
      Over.mapCongr,
      NatIso.ofComponents_inv_app, Category.assoc, TypeCat.Fun.toFun_apply, comp_apply]
  simp only [← CategoryTheory.Functor.map_comp_apply, ← op_comp]
  have hc := congrArg (fun f ↦ f.hom.app (op V) x) (α.equivariant g)
  change α.g.hom.hom.app (op V) ((torsorAut ξ.P g).hom.app (op V) x) =
    (torsorAut ξ'.P g).hom.app (op ((Over.map α.f.left).obj V))
      (α.g.hom.hom.app (op V) x) at hc
  erw [hc]
  congr 2

/-- A summand morphism induces an inertia morphism with its original underlying torsor map. -/
def toInertiaMap (ρ : G →* Aut X) {ξ ξ' : CoprodObj ρ}
    (α : ξ ⟶ ξ') : toInertiaObj ρ ξ ⟶ toInertiaObj ρ ξ' :=
  match α with
  | CategoryTheory.Sigma.SigmaHom.mk f =>
      RelativeInertia.homMk (forget (((ofOverFunctor S).mapAut _).comp ρ))
        (includeMap ρ _ f) (by exact toInertiaMap_comm ρ _ f)

/-- The inertia comparison's object and arrow maps preserve identities and composition. -/
private theorem toInertiaFunctor_laws (ρ : G →* Aut X) :
    (∀ ξ : CoprodObj ρ, toInertiaMap ρ (𝟙 ξ) = 𝟙 (toInertiaObj ρ ξ)) ∧
      (∀ (ξ ξ' ξ'' : CoprodObj ρ) (α : ξ ⟶ ξ') (β : ξ' ⟶ ξ''),
        toInertiaMap ρ (α ≫ β) = toInertiaMap ρ α ≫ toInertiaMap ρ β) := by
  constructor
  · rintro ⟨g, ξ⟩
    apply InducedCategory.hom_ext
    apply Subtype.ext
    rfl
  · intro ξ ξ' ξ'' α β
    cases α with
    | mk α =>
      cases β with
      | mk β =>
        apply InducedCategory.hom_ext
        apply Subtype.ext
        rfl

/-- The functor from fixed-locus quotient categories to inertia of the original quotient. -/
def toInertiaFunctor (ρ : G →* Aut X) :
    CoprodObj ρ ⥤ RelativeInertia (forget (((ofOverFunctor S).mapAut _).comp ρ)) where
  obj := toInertiaObj ρ
  map := toInertiaMap ρ
  map_id ξ := by exact (toInertiaFunctor_laws ρ).1 ξ
  map_comp {ξ ξ' ξ''} α β := by exact (toInertiaFunctor_laws ρ).2 ξ ξ' ξ'' α β

/-- The inertia comparison commutes with projection to schemes over the base. -/
private theorem toInertiaFunctor_over (ρ : G →* Aut X) :
    toInertiaFunctor ρ ⋙
      (StackOver.Groupoids.inertia (stack (((ofOverFunctor S).mapAut _).comp ρ))).p = p ρ := by
  refine CategoryTheory.Functor.ext (h_obj := ?_) ?_
  · rintro ⟨g, ξ⟩
    rfl
  · intro ξ ξ' α
    cases α
    rfl

/-- The inertia comparison over schemes preserves strongly cartesian morphisms. -/
private theorem toInertia_preservesStronglyCartesian (ρ : G →* Aut X) :
    (BasedFunctor.ofFunctor (toInertiaFunctor ρ)
      (toInertiaFunctor_over ρ)).PreservesStronglyCartesian := by
  letI : Functor.IsFibered.InGroupoids
      (StackOver.Groupoids.inertia (stack (((ofOverFunctor S).mapAut _).comp ρ))).p :=
    (StackOver.Groupoids.inertia (stack (((ofOverFunctor S).mapAut _).comp ρ))).toGroupoids.property
  intro ξ ξ' α hα
  change (StackOver.Groupoids.inertia (stack (((ofOverFunctor S).mapAut _).comp ρ))).p.IsStronglyCartesian
    _ (toInertiaMap ρ α)
  exact Functor.IsFibered.isStronglyCartesian_of_isCartesian
    (StackOver.Groupoids.inertia (stack (((ofOverFunctor S).mapAut _).comp ρ))).p
    ((StackOver.Groupoids.inertia (stack (((ofOverFunctor S).mapAut _).comp ρ))).p.map
      (toInertiaMap ρ α)) (toInertiaMap ρ α)

/-- The cartesian comparison from fixed-locus quotient categories to the quotient's inertia stack. -/
def toInertia (ρ : G →* Aut X) :
    CartesianBasedFunctor (p ρ)
      (StackOver.Groupoids.inertia (stack (((ofOverFunctor S).mapAut _).comp ρ))).p :=
  CartesianBasedFunctor.ofBasedFunctor
    (BasedFunctor.ofFunctor (toInertiaFunctor ρ) (by exact toInertiaFunctor_over ρ))
    (by exact toInertia_preservesStronglyCartesian ρ)

/-- The inertia of a quotient by a commutative group is the stack coproduct of its fixed-locus quotients. -/
instance inertia_coprod (ρ : G →* Aut X) :
    CartesianBasedFunctor.IsStackification (Scheme.fppfTopology.over S) (toInertia ρ) :=
  sorry

end AlgebraicGeometry.QuotientStack.InertiaCoprod
