/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.StalkGaloisAction
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Definition
public import Mathlib.FieldTheory.AbsoluteGaloisGroup

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Action ModuleCat
open AlgebraicGeometry

universe u

noncomputable section

namespace GaloisCohomology

variable (K Ksep : Type u) [Field K] [Field Ksep]
  [Algebra K Ksep] [IsSepClosure K Ksep]

/-- The geometric point of a field determined by a chosen separable closure. -/
def geometricPoint : Spec (.of Ksep) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K Ksep))

/-- The scheme map of a Galois automorphism lies over the base field. -/
theorem geometricPointIso_hom_comm (sigma : Gal(Ksep / K)) :
    Spec.map (CommRingCat.ofHom sigma.toRingHom) ≫ geometricPoint K Ksep =
      geometricPoint K Ksep := by
  unfold geometricPoint
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact sigma.commutes x

/-- The scheme map of an inverse Galois automorphism lies over the base field. -/
theorem geometricPointIso_inv_comm (sigma : Gal(Ksep / K)) :
    Spec.map (CommRingCat.ofHom sigma⁻¹.toRingHom) ≫ geometricPoint K Ksep =
      geometricPoint K Ksep :=
  geometricPointIso_hom_comm K Ksep sigma⁻¹

/-- The scheme maps of a Galois automorphism and its inverse compose to the identity over
the base field. -/
theorem geometricPointIso_hom_inv_id (sigma : Gal(Ksep / K)) :
    (Over.homMk (Spec.map (CommRingCat.ofHom sigma.toRingHom))
        (geometricPointIso_hom_comm K Ksep sigma) :
      Over.mk (geometricPoint K Ksep) ⟶ Over.mk (geometricPoint K Ksep)) ≫
      (Over.homMk (Spec.map (CommRingCat.ofHom sigma⁻¹.toRingHom))
        (geometricPointIso_inv_comm K Ksep sigma) :
        Over.mk (geometricPoint K Ksep) ⟶ Over.mk (geometricPoint K Ksep)) =
      𝟙 (Over.mk (geometricPoint K Ksep)) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  simp

/-- The scheme maps of an inverse Galois automorphism and the automorphism compose to the
identity over the base field. -/
theorem geometricPointIso_inv_hom_id (sigma : Gal(Ksep / K)) :
    (Over.homMk (Spec.map (CommRingCat.ofHom sigma⁻¹.toRingHom))
        (geometricPointIso_inv_comm K Ksep sigma) :
      Over.mk (geometricPoint K Ksep) ⟶ Over.mk (geometricPoint K Ksep)) ≫
      (Over.homMk (Spec.map (CommRingCat.ofHom sigma.toRingHom))
        (geometricPointIso_hom_comm K Ksep sigma) :
        Over.mk (geometricPoint K Ksep) ⟶ Over.mk (geometricPoint K Ksep)) =
      𝟙 (Over.mk (geometricPoint K Ksep)) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  simp

/-- A Galois automorphism induces an automorphism of the geometric point over the base field. -/
def geometricPointIso (sigma : Gal(Ksep / K)) :
    Over.mk (geometricPoint K Ksep) ≅ Over.mk (geometricPoint K Ksep) where
  hom := Over.homMk (Spec.map (CommRingCat.ofHom sigma.toRingHom))
    (geometricPointIso_hom_comm K Ksep sigma)
  inv := Over.homMk (Spec.map (CommRingCat.ofHom sigma⁻¹.toRingHom))
    (geometricPointIso_inv_comm K Ksep sigma)
  hom_inv_id := geometricPointIso_hom_inv_id K Ksep sigma
  inv_hom_id := geometricPointIso_inv_hom_id K Ksep sigma

/-- The small étale site point determined by a chosen separable closure. -/
abbrev etalePoint :=
  @Scheme.pointSmallEtale (Spec (.of K)) Ksep inferInstance
    (IsSepClosure.sep_closed K) (geometricPoint K Ksep)

/-- The action of a Galois automorphism on the fiber functor of the small étale point. -/
def etaleFiberAction (sigma : Gal(Ksep / K)) :
    (etalePoint K Ksep).fiber ⟶ (etalePoint K Ksep).fiber :=
  @Scheme.Etale.geometricPointFiberMap (Spec (.of K)) Ksep inferInstance
    (IsSepClosure.sep_closed K) (geometricPoint K Ksep) (geometricPointIso K Ksep sigma)

/-- The additive geometric fiber of a sheaf on the small étale site of a field. -/
def etaleFiber
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :
    AddCommGrpCat.{u} :=
  ((etalePoint K Ksep).sheafFiber :
    Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}).obj F

/-- The additive stalk endomorphism induced by a Galois automorphism of the geometric point. -/
def etaleStalkAction
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
    (sigma : Gal(Ksep / K)) :
    etaleFiber K Ksep F ⟶ etaleFiber K Ksep F :=
  (GrothendieckTopology.Point.Hom.sheafFiber
    (⟨etaleFiberAction K Ksep sigma⟩ : etalePoint K Ksep ⟶ etalePoint K Ksep)).app F

/-- The identity Galois automorphism acts identically on the additive geometric stalk. -/
theorem etaleStalkAction_map_one
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :
    ModuleCat.ofHom (etaleStalkAction K Ksep F 1).hom.toIntLinearMap =
      (1 : End (ModuleCat.of ℤ (etaleFiber K Ksep F))) := by
  have h : (geometricPointIso K Ksep 1).hom =
      𝟙 (Over.mk (geometricPoint K Ksep)) := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (1 : Gal(Ksep / K)).toRingHom) = 𝟙 _
    rw [← Spec.map_id]
    rfl
  have hp : (⟨etaleFiberAction K Ksep 1⟩ : etalePoint K Ksep ⟶ etalePoint K Ksep) =
      𝟙 (etalePoint K Ksep) := by
    apply GrothendieckTopology.Point.hom_ext
    dsimp only [etaleFiberAction, Scheme.Etale.geometricPointFiberMap]
    rw [h]
    simp only [op_id, Functor.map_id, Functor.whiskerLeft_id]
    rfl
  have ha : etaleStalkAction K Ksep F 1 = 𝟙 (etaleFiber K Ksep F) := by
    unfold etaleStalkAction
    rw [hp, GrothendieckTopology.Point.Hom.sheafFiber_id]
    rfl
  rw [ha]
  rfl

/-- Composition of Galois automorphisms agrees with composition of their additive stalk maps. -/
theorem etaleStalkAction_map_mul
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
    (sigma tau : Gal(Ksep / K)) :
    ModuleCat.ofHom (etaleStalkAction K Ksep F (sigma * tau)).hom.toIntLinearMap =
      ModuleCat.ofHom (etaleStalkAction K Ksep F tau).hom.toIntLinearMap ≫
        ModuleCat.ofHom (etaleStalkAction K Ksep F sigma).hom.toIntLinearMap := by
  have h : (geometricPointIso K Ksep (sigma * tau)).hom =
      (geometricPointIso K Ksep sigma).hom ≫ (geometricPointIso K Ksep tau).hom := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (sigma * tau).toRingHom) =
      Spec.map (CommRingCat.ofHom sigma.toRingHom) ≫
        Spec.map (CommRingCat.ofHom tau.toRingHom)
    rw [← Spec.map_comp]
    rfl
  let p (g : Gal(Ksep/K)) : End (etalePoint K Ksep) := ⟨etaleFiberAction K Ksep g⟩
  have hp : p (sigma * tau) = p sigma ≫ p tau := by
    apply GrothendieckTopology.Point.hom_ext
    change etaleFiberAction K Ksep (sigma * tau) =
      etaleFiberAction K Ksep tau ≫ etaleFiberAction K Ksep sigma
    dsimp only [etaleFiberAction, Scheme.Etale.geometricPointFiberMap]
    rw [h, op_comp, Functor.map_comp, Functor.whiskerLeft_comp]
    rfl
  have ha : etaleStalkAction K Ksep F (sigma * tau) =
      etaleStalkAction K Ksep F tau ≫ etaleStalkAction K Ksep F sigma := by
    change ((p (sigma * tau)).sheafFiber (A := AddCommGrpCat.{u})).app F =
      ((p tau).sheafFiber (A := AddCommGrpCat.{u})).app F ≫
        ((p sigma).sheafFiber (A := AddCommGrpCat.{u})).app F
    rw [hp, GrothendieckTopology.Point.Hom.sheafFiber_comp]
    rfl
  rw [ha]
  rfl

/-- The Galois action on an additive geometric stalk has open stabilizers. -/
theorem etaleStalkAction_openStabilizer
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :
    openStabilizer ℤ (Gal(Ksep / K))
      { V := ModuleCat.of ℤ (etaleFiber K Ksep F)
        ρ := { toFun := fun sigma ↦
                 ModuleCat.ofHom (etaleStalkAction K Ksep F sigma).hom.toIntLinearMap
               map_one' := etaleStalkAction_map_one K Ksep F
               map_mul' := etaleStalkAction_map_mul K Ksep F } } := sorry

/-- The discrete integral Galois module carried by an additive geometric stalk. -/
def etaleStalk
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :
    DiscreteModuleCat ℤ (Gal(Ksep / K)) :=
  ⟨{ V := ModuleCat.of ℤ (etaleFiber K Ksep F)
     ρ := { toFun := fun sigma ↦
              ModuleCat.ofHom (etaleStalkAction K Ksep F sigma).hom.toIntLinearMap
            map_one' := etaleStalkAction_map_one K Ksep F
            map_mul' := etaleStalkAction_map_mul K Ksep F } },
    etaleStalkAction_openStabilizer K Ksep F⟩

/-- The underlying module of the discrete Galois stalk is the additive geometric stalk. -/
theorem etaleStalk_obj
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleStalk K Ksep F).obj.V = ModuleCat.of ℤ (etaleFiber K Ksep F) := rfl

/-- The Galois action on the discrete stalk is induced by geometric-point automorphisms. -/
theorem etaleStalk_action
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
    (sigma : Gal(Ksep / K)) :
    (etaleStalk K Ksep F).obj.ρ sigma = ModuleCat.ofHom
      (etaleStalkAction K Ksep F sigma).hom.toIntLinearMap := rfl

end GaloisCohomology

end
