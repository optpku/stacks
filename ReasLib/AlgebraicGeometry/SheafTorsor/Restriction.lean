/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Sites.Torsor.Iso

/-!
# Restriction of fppf sheaves of groups and torsors

Inverse image of sheaves of types and groups along morphisms in `(Sch/S)_fppf`,
together with the inverse image of a torsor under a sheaf of groups.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.SheafTorsors

variable {S : Scheme.{u}}

/-- Restriction of an fppf sheaf of types from `(Sch/S)_fppf` to `(Sch/U)_fppf`. -/
def restrict (U : Over S) :
    Sheaf (Scheme.fppfTopology.over S) (Type u) ⥤
      Sheaf (Scheme.fppfTopology.over U.left) (Type u) :=
  (Over.map U.hom).sheafPushforwardContinuous (Type u)
    (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over S)

/-- Inverse image of an fppf sheaf of types along a morphism in `Over S`. -/
def inverseImage {U U' : Over S} (f : U ⟶ U') :
    Sheaf (Scheme.fppfTopology.over U'.left) (Type u) ⥤
      Sheaf (Scheme.fppfTopology.over U.left) (Type u) :=
  (Over.map f.left).sheafPushforwardContinuous (Type u)
    (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over U'.left)

/-- Restriction of an fppf sheaf of groups from `(Sch/S)_fppf` to `(Sch/U)_fppf`. -/
def restrictGrp (U : Over S) :
    Sheaf (Scheme.fppfTopology.over S) GrpCat.{u} ⥤
      Sheaf (Scheme.fppfTopology.over U.left) GrpCat.{u} :=
  (Over.map U.hom).sheafPushforwardContinuous GrpCat.{u}
    (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over S)

/-- Inverse image of an fppf sheaf of groups along a morphism in `Over S`. -/
def inverseImageGrp {U U' : Over S} (f : U ⟶ U') :
    Sheaf (Scheme.fppfTopology.over U'.left) GrpCat.{u} ⥤
      Sheaf (Scheme.fppfTopology.over U.left) GrpCat.{u} :=
  (Over.map f.left).sheafPushforwardContinuous GrpCat.{u}
    (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over U'.left)

/-- Inverse image along an identity morphism of `Over S` is the identity functor. -/
def inverseImageId (U : Over S) :
    inverseImage (𝟙 U) ≅ 𝟭 (Sheaf (Scheme.fppfTopology.over U.left) (Type u)) :=
  Functor.sheafPushforwardContinuousId' (Over.mapId U.left) (Type u)
    (Scheme.fppfTopology.over U.left)

/-- Inverse image is contravariant for composition in `Over S`. -/
def inverseImageComp {U U' U'' : Over S} (f : U ⟶ U') (g : U' ⟶ U'') :
    inverseImage g ⋙ inverseImage f ≅ inverseImage (f ≫ g) :=
  Functor.sheafPushforwardContinuousComp' (Over.mapComp f.left g.left).symm (Type u)
    (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over U'.left)
    (Scheme.fppfTopology.over U''.left)

/-- Restricting from `S` to `U'` and then pulling back along `f : U ⟶ U'` is
restriction to `U`. -/
def restrictIso {U U' : Over S} (f : U ⟶ U') :
    restrict U' ⋙ inverseImage f ≅ restrict U :=
  Functor.sheafPushforwardContinuousComp'
    ((Over.mapComp f.left U'.hom).symm ≪≫ Over.mapCongr (f.left ≫ U'.hom) U.hom f.w)
    (Type u) (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over U'.left)
    (Scheme.fppfTopology.over S)

/-- Restricting a sheaf of groups from `S` to `U'` and then pulling back along
`f : U ⟶ U'` is restriction to `U`. -/
def restrictGrpIso {U U' : Over S} (f : U ⟶ U') :
    restrictGrp U' ⋙ inverseImageGrp f ≅ restrictGrp U :=
  Functor.sheafPushforwardContinuousComp'
    ((Over.mapComp f.left U'.hom).symm ≪≫ Over.mapCongr (f.left ≫ U'.hom) U.hom f.w)
    GrpCat.{u} (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over U'.left)
    (Scheme.fppfTopology.over S)

/-- Group sections of `𝒢|_U` over `V` identify with group sections of the inverse
image of `𝒢|_U'`. -/
def restrictGrpIso_app {U U' : Over S} (f : U ⟶ U')
    (𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}) (V : Over U.left) :
    ((inverseImageGrp f).obj ((restrictGrp U').obj 𝒢)).obj.obj (op V) ≅
      ((restrictGrp U).obj 𝒢).obj.obj (op V) :=
  ((sheafToPresheaf (Scheme.fppfTopology.over U.left) GrpCat.{u}).mapIso
      ((restrictGrpIso f).app 𝒢)).app (op V)

/-- The transported action of a section of `𝒢|_U` on a section of `f⁻¹ P`. -/
def inverseImageTorsor_smul {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {U U' : Over S} (f : U ⟶ U') (P : Sheaf.Torsor ((restrictGrp U').obj 𝒢))
    (V : Over U.left) (γ : ((restrictGrp U).obj 𝒢).obj.obj (op V))
    (x : ((inverseImage f).obj P.carrier).obj.obj (op V)) :
    ((inverseImage f).obj P.carrier).obj.obj (op V) :=
  (P.mulAction ((Over.map f.left).obj V)).smul
    ((Iso.groupIsoToMulEquiv (restrictGrpIso_app f 𝒢 V)).symm γ) x

/-- The transported action of the unit section is the identity. -/
theorem inverseImageTorsor_one_smul
    {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {U U' : Over S} (f : U ⟶ U') (P : Sheaf.Torsor ((restrictGrp U').obj 𝒢))
    (V : Over U.left) (x : ((inverseImage f).obj P.carrier).obj.obj (op V)) :
    inverseImageTorsor_smul f P V 1 x = x := by
  dsimp only [inverseImageTorsor_smul]
  rw [map_one]
  exact (P.mulAction _).one_smul x

/-- The transported action respects multiplication of group sections. -/
theorem inverseImageTorsor_mul_smul
    {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {U U' : Over S} (f : U ⟶ U') (P : Sheaf.Torsor ((restrictGrp U').obj 𝒢))
    (V : Over U.left) (γ δ : ((restrictGrp U).obj 𝒢).obj.obj (op V))
    (x : ((inverseImage f).obj P.carrier).obj.obj (op V)) :
    inverseImageTorsor_smul f P V (γ * δ) x =
      inverseImageTorsor_smul f P V γ (inverseImageTorsor_smul f P V δ x) := by
  dsimp only [inverseImageTorsor_smul]
  rw [map_mul]
  exact (P.mulAction _).mul_smul _ _ x

/-- The sectionwise group action transported to the inverse-image carrier. -/
@[reducible]
def inverseImageTorsorMulAction
    {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {U U' : Over S} (f : U ⟶ U') (P : Sheaf.Torsor ((restrictGrp U').obj 𝒢))
    (V : Over U.left) :
    MulAction (((restrictGrp U).obj 𝒢).obj.obj (op V))
      (((inverseImage f).obj P.carrier).obj.obj (op V)) where
  smul := inverseImageTorsor_smul f P V
  one_smul := inverseImageTorsor_one_smul f P V
  mul_smul := inverseImageTorsor_mul_smul f P V

/-- Restriction of inverse-image sections commutes with the transported action. -/
theorem inverseImageTorsor_act_naturality
    {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {U U' : Over S} (f : U ⟶ U') (P : Sheaf.Torsor ((restrictGrp U').obj 𝒢))
    {V W : Over U.left} (a : W ⟶ V)
    (γ : ((restrictGrp U).obj 𝒢).obj.obj (op V))
    (x : ((inverseImage f).obj P.carrier).obj.obj (op V)) :
    ((inverseImage f).obj P.carrier).obj.map a.op
        ((inverseImageTorsorMulAction f P V).smul γ x) =
      (inverseImageTorsorMulAction f P W).smul
        (((restrictGrp U).obj 𝒢).obj.map a.op γ)
        (((inverseImage f).obj P.carrier).obj.map a.op x) := by
  change P.carrier.obj.map ((Over.map f.left).map a).op
      ((P.mulAction _).smul
        ((Iso.groupIsoToMulEquiv (restrictGrpIso_app f 𝒢 V)).symm γ) x) =
    (P.mulAction _).smul
      ((Iso.groupIsoToMulEquiv (restrictGrpIso_app f 𝒢 W)).symm
        (((restrictGrp U).obj 𝒢).obj.map a.op γ))
      (P.carrier.obj.map ((Over.map f.left).map a).op x)
  rw [P.act_naturality]
  congr 1
  exact (ConcreteCategory.congr_hom
    (((restrictGrpIso f).inv.app 𝒢).hom.naturality a.op) γ).symm

/-- The transported action is pretransitive on sections. -/
theorem inverseImageTorsor_isPretransitive
    {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {U U' : Over S} (f : U ⟶ U') (P : Sheaf.Torsor ((restrictGrp U').obj 𝒢))
    (V : Over U.left) :
    @MulAction.IsPretransitive (((restrictGrp U).obj 𝒢).obj.obj (op V))
      (((inverseImage f).obj P.carrier).obj.obj (op V))
      (inverseImageTorsorMulAction f P V).toSMul := by
  letI := inverseImageTorsorMulAction f P V
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨γ, hγ⟩ := (P.isPretransitive ((Over.map f.left).obj V)).exists_smul_eq x y
  refine ⟨Iso.groupIsoToMulEquiv (restrictGrpIso_app f 𝒢 V) γ, ?_⟩
  change (P.mulAction _).smul
    ((Iso.groupIsoToMulEquiv (restrictGrpIso_app f 𝒢 V)).symm
      (Iso.groupIsoToMulEquiv (restrictGrpIso_app f 𝒢 V) γ)) x = y
  rw [MulEquiv.symm_apply_apply]
  exact hγ

/-- The transported action is free on sections. -/
theorem inverseImageTorsor_isCancelSMul
    {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {U U' : Over S} (f : U ⟶ U') (P : Sheaf.Torsor ((restrictGrp U').obj 𝒢))
    (V : Over U.left) :
    @IsCancelSMul (((restrictGrp U).obj 𝒢).obj.obj (op V))
      (((inverseImage f).obj P.carrier).obj.obj (op V))
      (inverseImageTorsorMulAction f P V).toSMul := by
  letI := inverseImageTorsorMulAction f P V
  refine { left_cancel' := ?_, right_cancel' := ?_ }
  · intro γ x y h
    exact (P.isCancelSMul ((Over.map f.left).obj V)).left_cancel' _ _ _ h
  · intro γ δ x h
    apply (Iso.groupIsoToMulEquiv (restrictGrpIso_app f 𝒢 V)).symm.injective
    exact (P.isCancelSMul ((Over.map f.left).obj V)).right_cancel' _ _ _ h

/-- The inverse-image carrier of a torsor is locally nonempty. -/
theorem inverseImageTorsor_locallyNonempty
    {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {U U' : Over S} (f : U ⟶ U') (P : Sheaf.Torsor ((restrictGrp U').obj 𝒢))
    (V : Over U.left) :
    ∃ R : Sieve V, R ∈ (Scheme.fppfTopology.over U.left) V ∧
      ∀ ⦃W : Over U.left⦄ (a : W ⟶ V), R a →
        Nonempty (((inverseImage f).obj P.carrier).obj.obj (op W)) := by
  obtain ⟨R, hR, h⟩ := P.locallyNonempty ((Over.map f.left).obj V)
  refine ⟨R.functorPullback (Over.map f.left),
    (Over.map f.left).cover_lift _ _ hR, ?_⟩
  intro W a ha
  exact h ((Over.map f.left).map a) ha

/-- Inverse image of a restricted torsor along a morphism of schemes over the base. -/
def inverseImageTorsor {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {U U' : Over S} (f : U ⟶ U') (P : Sheaf.Torsor ((restrictGrp U').obj 𝒢)) :
    Sheaf.Torsor ((restrictGrp U).obj 𝒢) where
  carrier := (inverseImage f).obj P.carrier
  mulAction := inverseImageTorsorMulAction f P
  act_naturality := inverseImageTorsor_act_naturality f P
  isPretransitive := inverseImageTorsor_isPretransitive f P
  isCancelSMul := inverseImageTorsor_isCancelSMul f P
  locallyNonempty := inverseImageTorsor_locallyNonempty f P

/-- The carrier of `inverseImageTorsor f P` is the inverse image of the carrier of `P`. -/
theorem inverseImageTorsor_carrier {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {U U' : Over S} (f : U ⟶ U') (P : Sheaf.Torsor ((restrictGrp U').obj 𝒢)) :
    (inverseImageTorsor f P).carrier = (inverseImage f).obj P.carrier := rfl

/-- The identity comparison of inverse-image torsors is equivariant. -/
theorem inverseImageTorsorId_hom_comm
    {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} {U : Over S}
    (P : Sheaf.Torsor ((restrictGrp U).obj 𝒢)) (V : Over U.left)
    (γ : ((restrictGrp U).obj 𝒢).obj.obj (op V))
    (x : (inverseImageTorsor (𝟙 U) P).carrier.obj.obj (op V)) :
    ((inverseImageId U).hom.app P.carrier).hom.app (op V)
        (((inverseImageTorsor (𝟙 U) P).mulAction V).smul γ x) =
      (P.mulAction V).smul γ
        (((inverseImageId U).hom.app P.carrier).hom.app (op V) x) := by
  change P.carrier.obj.map ((Over.mapId U.left).inv.app V).op
      ((P.mulAction _).smul _ x) =
    (P.mulAction V).smul γ
      (P.carrier.obj.map ((Over.mapId U.left).inv.app V).op x)
  rw [P.act_naturality]
  congr 1
  change 𝒢.obj.map _ (𝒢.obj.map _ γ) = γ
  rw [← Functor.map_comp_apply]
  calc
    𝒢.obj.map _ γ = 𝒢.obj.map (𝟙 _) γ := by
      apply ConcreteCategory.congr_hom
      apply 𝒢.obj.congr_map
      apply Quiver.Hom.unop_inj
      apply Over.OverMorphism.ext
      change (𝟙 V.left ≫ 𝟙 V.left ≫ 𝟙 V.left) = 𝟙 V.left
      simp
    _ = γ := by simp

/-- Inverse image along an identity is canonically isomorphic to the original torsor. -/
def inverseImageTorsorId {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {U : Over S} (P : Sheaf.Torsor ((restrictGrp U).obj 𝒢)) :
    Sheaf.Torsor.Iso (inverseImageTorsor (𝟙 U) P) P :=
  Sheaf.Torsor.Iso.ofCarrierIso ((inverseImageId U).app P.carrier)
    (inverseImageTorsorId_hom_comm P)

/-- The composite comparison of inverse-image torsors is equivariant. -/
theorem inverseImageTorsorComp_hom_comm
    {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} {U U' U'' : Over S}
    (f : U ⟶ U') (g : U' ⟶ U'') (P : Sheaf.Torsor ((restrictGrp U'').obj 𝒢))
    (V : Over U.left) (γ : ((restrictGrp U).obj 𝒢).obj.obj (op V))
    (x : (inverseImageTorsor (f ≫ g) P).carrier.obj.obj (op V)) :
    ((inverseImageComp f g).inv.app P.carrier).hom.app (op V)
        (((inverseImageTorsor (f ≫ g) P).mulAction V).smul γ x) =
      ((inverseImageTorsor f (inverseImageTorsor g P)).mulAction V).smul γ
        (((inverseImageComp f g).inv.app P.carrier).hom.app (op V) x) := by
  change P.carrier.obj.map ((Over.mapComp f.left g.left).inv.app V).op
      ((P.mulAction _).smul _ x) =
    (P.mulAction _).smul _
      (P.carrier.obj.map ((Over.mapComp f.left g.left).inv.app V).op x)
  rw [P.act_naturality]
  congr 1
  change 𝒢.obj.map _ (𝒢.obj.map _ γ) = 𝒢.obj.map _ (𝒢.obj.map _ γ)
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  apply ConcreteCategory.congr_hom
  apply 𝒢.obj.congr_map
  apply Quiver.Hom.unop_inj
  apply Over.OverMorphism.ext
  change (𝟙 V.left ≫ 𝟙 V.left ≫ 𝟙 V.left) =
    ((𝟙 V.left ≫ 𝟙 V.left) ≫ (𝟙 V.left ≫ 𝟙 V.left))
  simp

/-- Inverse image of torsors is contravariant for composition of scheme maps. -/
def inverseImageTorsorComp {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {U U' U'' : Over S} (f : U ⟶ U') (g : U' ⟶ U'')
    (P : Sheaf.Torsor ((restrictGrp U'').obj 𝒢)) :
    Sheaf.Torsor.Iso (inverseImageTorsor (f ≫ g) P)
      (inverseImageTorsor f (inverseImageTorsor g P)) :=
  Sheaf.Torsor.Iso.ofCarrierIso ((inverseImageComp f g).app P.carrier).symm
    (inverseImageTorsorComp_hom_comm f g P)

/-- Inverse image of an equivariant morphism of torsors is equivariant. -/
theorem inverseImageTorsorMap_hom_comm
    {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} {U U' : Over S}
    (f : U ⟶ U') {P Q : Sheaf.Torsor ((restrictGrp U').obj 𝒢)}
    (α : Sheaf.Torsor.Iso P Q) (V : Over U.left)
    (γ : ((restrictGrp U).obj 𝒢).obj.obj (op V))
    (x : (inverseImageTorsor f P).carrier.obj.obj (op V)) :
    ((inverseImage f).map (Sheaf.Torsor.Iso.toCarrierIso α).hom).hom.app (op V)
        (((inverseImageTorsor f P).mulAction V).smul γ x) =
      ((inverseImageTorsor f Q).mulAction V).smul γ
        (((inverseImage f).map (Sheaf.Torsor.Iso.toCarrierIso α).hom).hom.app (op V) x) := by
  exact (@Iso.hom _ Sheaf.Torsor.category _ _ α).comm
    ((Over.map f.left).obj V) _ x

/-- Inverse image transports torsor isomorphisms using their actual carrier maps. -/
def inverseImageTorsorMap {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {U U' : Over S} (f : U ⟶ U') {P Q : Sheaf.Torsor ((restrictGrp U').obj 𝒢)}
    (α : Sheaf.Torsor.Iso P Q) :
    Sheaf.Torsor.Iso (inverseImageTorsor f P) (inverseImageTorsor f Q) :=
  Sheaf.Torsor.Iso.ofCarrierIso
    ((inverseImage f).mapIso (Sheaf.Torsor.Iso.toCarrierIso α))
    (inverseImageTorsorMap_hom_comm f α)

/-- Restriction of a sheaf of groups to `U` is `𝒢|_U`. -/
theorem restrictGrp_obj (U : Over S)
    (𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}) :
    (restrictGrp U).obj 𝒢 =
      ((Over.map U.hom).sheafPushforwardContinuous GrpCat.{u}
        (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over S)).obj 𝒢 := rfl

end AlgebraicGeometry.SheafTorsors
