/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.StalkGaloisSet
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Definition
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

open CategoryTheory Opposite
open CategoryTheory.Action ModuleCat
open AlgebraicGeometry

@[expose] public section

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Etale

/-- The additive étale stalk at the embedded separable closure of the image residue field. -/
def stalkAddCommGrp (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :
    AddCommGrpCat.{u} :=
  ((etalePoint K s).sheafFiber (A := AddCommGrpCat.{u})).obj F

/-- A residue-field Galois automorphism induces an additive endomorphism of the étale stalk. -/
def stalkGaloisModuleAction (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
    (σ : s.absoluteGaloisGroup) :
    stalkAddCommGrp K s F ⟶ stalkAddCommGrp K s F :=
  (GrothendieckTopology.Point.Hom.sheafFiber
    (⟨geometricPointFiberMap (geometricPointHom K s)
      (geometricPointGaloisIso K s σ)⟩ : etalePoint K s ⟶ etalePoint K s)
    (A := AddCommGrpCat.{u})).app F

/-- The identity residue-field automorphism acts identically on the additive stalk. -/
theorem stalkGaloisModuleFromFieldValuedPoint_action_one
    (K : Type u) [Field K] (point : FieldValuedPoint (Spec (.of K)))
    (isAlgClosed : IsAlgClosed point.K)
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :
    ModuleCat.ofHom
      (stalkGaloisModuleAction K ⟨point, isAlgClosed⟩ F 1).hom.toIntLinearMap =
        𝟙 (ModuleCat.of ℤ (stalkAddCommGrp K ⟨point, isAlgClosed⟩ F)) := sorry

/-- Multiplication of residue-field automorphisms gives composition of their left stalk actions. -/
theorem stalkGaloisModuleFromFieldValuedPoint_action_mul
    (K : Type u) [Field K] (point : FieldValuedPoint (Spec (.of K)))
    (isAlgClosed : IsAlgClosed point.K)
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
    (σ τ : Gal(point.separableClosureOfAlgClosed isAlgClosed/(Spec (.of K)).residueField point.image)) :
    ModuleCat.ofHom
      (stalkGaloisModuleAction K ⟨point, isAlgClosed⟩ F (σ * τ)).hom.toIntLinearMap =
        ModuleCat.ofHom (stalkGaloisModuleAction K ⟨point, isAlgClosed⟩ F τ).hom.toIntLinearMap ≫
          ModuleCat.ofHom (stalkGaloisModuleAction K ⟨point, isAlgClosed⟩ F σ).hom.toIntLinearMap :=
  sorry

/-- The integral linear action of the residue-field Galois group on the additive étale stalk. -/
def stalkGaloisModuleFromFieldValuedPoint.action (K : Type u) [Field K]
    (point : FieldValuedPoint (Spec (.of K))) (isAlgClosed : IsAlgClosed point.K)
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :
    Action (ModuleCat.{u} ℤ)
      Gal(point.separableClosureOfAlgClosed isAlgClosed /
        (Spec (.of K)).residueField point.image) where
  V := ModuleCat.of ℤ (stalkAddCommGrp K ⟨point, isAlgClosed⟩ F)
  ρ :=
    { toFun := fun σ ↦ ModuleCat.ofHom
        (stalkGaloisModuleAction K ⟨point, isAlgClosed⟩ F σ).hom.toIntLinearMap
      map_one' := stalkGaloisModuleFromFieldValuedPoint_action_one K point isAlgClosed F
      map_mul' := stalkGaloisModuleFromFieldValuedPoint_action_mul K point isAlgClosed F }

/-- Every element of the additive étale stalk has open stabilizer in the residue-field Galois group. -/
theorem stalkGaloisModuleFromFieldValuedPoint_openStabilizer
    (K : Type u) [Field K] (point : FieldValuedPoint (Spec (.of K)))
    (isAlgClosed : IsAlgClosed point.K)
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :
    openStabilizer ℤ
      Gal(point.separableClosureOfAlgClosed isAlgClosed /
        (Spec (.of K)).residueField point.image)
      (stalkGaloisModuleFromFieldValuedPoint.action K point isAlgClosed F) := sorry

/-- The additive étale stalk as a discrete continuous residue-field Galois module. -/
def stalkGaloisModuleFromFieldValuedPoint.obj (K : Type u) [Field K]
    (point : FieldValuedPoint (Spec (.of K))) (isAlgClosed : IsAlgClosed point.K)
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :
    DiscreteModuleCat ℤ
      Gal(point.separableClosureOfAlgClosed isAlgClosed /
        (Spec (.of K)).residueField point.image) :=
  ⟨stalkGaloisModuleFromFieldValuedPoint.action K point isAlgClosed F,
    stalkGaloisModuleFromFieldValuedPoint_openStabilizer K point isAlgClosed F⟩

/-- A morphism of abelian étale sheaves induces a Galois-equivariant additive stalk map. -/
theorem stalkGaloisModuleFromFieldValuedPoint_map_comm
    (K : Type u) [Field K] (point : FieldValuedPoint (Spec (.of K)))
    (isAlgClosed : IsAlgClosed point.K)
    {F G : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}} (f : F ⟶ G)
    (σ : Gal(point.separableClosureOfAlgClosed isAlgClosed/(Spec (.of K)).residueField point.image)) :
    (stalkGaloisModuleFromFieldValuedPoint.obj K point isAlgClosed F).obj.ρ σ ≫
        ModuleCat.ofHom (((etalePoint K ⟨point, isAlgClosed⟩).sheafFiber
          (A := AddCommGrpCat.{u})).map f).hom.toIntLinearMap =
      ModuleCat.ofHom (((etalePoint K ⟨point, isAlgClosed⟩).sheafFiber
          (A := AddCommGrpCat.{u})).map f).hom.toIntLinearMap ≫
        (stalkGaloisModuleFromFieldValuedPoint.obj K point isAlgClosed G).obj.ρ σ := sorry

/-- The Galois-module morphism induced by the additive stalk map of a sheaf morphism. -/
def stalkGaloisModuleFromFieldValuedPoint.map (K : Type u) [Field K]
    (point : FieldValuedPoint (Spec (.of K))) (isAlgClosed : IsAlgClosed point.K)
    {F G : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}} (f : F ⟶ G) :
    stalkGaloisModuleFromFieldValuedPoint.obj K point isAlgClosed F ⟶
      stalkGaloisModuleFromFieldValuedPoint.obj K point isAlgClosed G :=
  ObjectProperty.homMk
    { hom := ModuleCat.ofHom (((etalePoint K ⟨point, isAlgClosed⟩).sheafFiber
        (A := AddCommGrpCat.{u})).map f).hom.toIntLinearMap
      comm := stalkGaloisModuleFromFieldValuedPoint_map_comm K point isAlgClosed f }

/-- The additive stalk map of an identity sheaf morphism is the identity module morphism. -/
theorem stalkGaloisModuleFromFieldValuedPoint_map_id
    (K : Type u) [Field K] (point : FieldValuedPoint (Spec (.of K)))
    (isAlgClosed : IsAlgClosed point.K)
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :
    stalkGaloisModuleFromFieldValuedPoint.map K point isAlgClosed (𝟙 F) =
      𝟙 (stalkGaloisModuleFromFieldValuedPoint.obj K point isAlgClosed F) := sorry

/-- Additive stalk maps preserve composition of sheaf morphisms. -/
theorem stalkGaloisModuleFromFieldValuedPoint_map_comp
    (K : Type u) [Field K] (point : FieldValuedPoint (Spec (.of K)))
    (isAlgClosed : IsAlgClosed point.K)
    {F G H : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}}
    (f : F ⟶ G) (g : G ⟶ H) :
    stalkGaloisModuleFromFieldValuedPoint.map K point isAlgClosed (f ≫ g) =
      stalkGaloisModuleFromFieldValuedPoint.map K point isAlgClosed f ≫
        stalkGaloisModuleFromFieldValuedPoint.map K point isAlgClosed g := sorry

/-- The additive étale stalk functor for an algebraically closed field-valued point, with its
continuous action of the Galois group of the embedded separable residue-field closure. -/
def stalkGaloisModuleFromFieldValuedPoint (K : Type u) [Field K]
    (point : FieldValuedPoint (Spec (.of K))) (isAlgClosed : IsAlgClosed point.K) :
    Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u} ⥤
      DiscreteModuleCat ℤ
        Gal(point.separableClosureOfAlgClosed isAlgClosed /
          (Spec (.of K)).residueField point.image) where
  obj := stalkGaloisModuleFromFieldValuedPoint.obj K point isAlgClosed
  map := stalkGaloisModuleFromFieldValuedPoint.map K point isAlgClosed
  map_id := stalkGaloisModuleFromFieldValuedPoint_map_id K point isAlgClosed
  map_comp := stalkGaloisModuleFromFieldValuedPoint_map_comp K point isAlgClosed

/-- The additive stalk functor of an algebraically closed field-valued point of a field spectrum
is an equivalence with discrete continuous residue-field Galois modules. -/
instance stalkGaloisModuleFromFieldValuedPoint_isEquivalence
    (K : Type u) [Field K] (point : FieldValuedPoint (Spec (.of K)))
    (isAlgClosed : IsAlgClosed point.K) :
    (stalkGaloisModuleFromFieldValuedPoint K point isAlgClosed).IsEquivalence := sorry

/-- The additive stalk functor at an algebraically closed field-valued point preserves
finite limits. -/
instance stalkGaloisModuleFromFieldValuedPoint_preservesFiniteLimits
    (K : Type u) [Field K] (point : FieldValuedPoint (Spec (.of K)))
    (isAlgClosed : IsAlgClosed point.K) :
    Limits.PreservesFiniteLimits
      (stalkGaloisModuleFromFieldValuedPoint K point isAlgClosed) := sorry

/-- The additive stalk functor at an algebraically closed field-valued point preserves
finite colimits. -/
instance stalkGaloisModuleFromFieldValuedPoint_preservesFiniteColimits
    (K : Type u) [Field K] (point : FieldValuedPoint (Spec (.of K)))
    (isAlgClosed : IsAlgClosed point.K) :
    Limits.PreservesFiniteColimits
      (stalkGaloisModuleFromFieldValuedPoint K point isAlgClosed) := sorry

/-- The stalk functor from abelian étale sheaves to discrete continuous Galois modules is
additive at every algebraically closed field-valued point. -/
instance stalkGaloisModuleFromFieldValuedPoint_additive
    (K : Type u) [Field K] (point : FieldValuedPoint (Spec (.of K)))
    (isAlgClosed : IsAlgClosed point.K) :
    (stalkGaloisModuleFromFieldValuedPoint K point isAlgClosed).Additive := sorry

/-- The additive étale stalk functor at a geometric point, equipped with its continuous
residue-field Galois action. -/
abbrev stalkGaloisModule (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K))) :
    Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u} ⥤
      DiscreteModuleCat ℤ s.absoluteGaloisGroup :=
  stalkGaloisModuleFromFieldValuedPoint K s.toFieldValuedPoint s.isAlgClosed

/-- The discrete continuous residue-field Galois module given by the additive étale stalk. -/
def stalkGaloisModuleObj (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :
    DiscreteModuleCat ℤ s.absoluteGaloisGroup :=
  (stalkGaloisModule K s).obj F

/-- The carrier of the Galois stalk module is the additive stalk at the separable point. -/
theorem stalkGaloisModule_obj_carrier (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :
    ((stalkGaloisModule K s).obj F).obj.V =
      ModuleCat.of ℤ (stalkAddCommGrp K s F) := rfl

/-- The Galois action on the additive stalk is induced by the corresponding separable-point
automorphism. -/
theorem stalkGaloisModule_smul (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
    (σ : s.absoluteGaloisGroup) :
    ((stalkGaloisModule K s).obj F).obj.ρ σ =
      ModuleCat.ofHom (stalkGaloisModuleAction K s F σ).hom.toIntLinearMap := rfl

/-- The additive étale stalk at any geometric point of a field spectrum induces an equivalence
with discrete continuous modules for the absolute Galois group of its image residue field. -/
theorem stalkGaloisModule_isEquivalence
    (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K))) :
    (stalkGaloisModule K s).IsEquivalence :=
  stalkGaloisModuleFromFieldValuedPoint_isEquivalence K s.toFieldValuedPoint s.isAlgClosed

/-- The inclusion of the embedded separable closure into the geometric-point field induces
a natural additive map from the separable-point stalk to the geometric stalk. -/
def stalkAddCommGrpToGeometricStalk (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K))) :
    (etalePoint K s).sheafFiber (A := AddCommGrpCat.{u}) ⟶
      (@Scheme.pointSmallEtale _ s.K s.field
        (@IsSepClosed.of_isAlgClosed s.K s.field s.isAlgClosed) s.hom).sheafFiber :=
  GrothendieckTopology.Point.Hom.sheafFiber
    (⟨Functor.whiskerLeft (Etale.forget (Spec (.of K)))
      (coyoneda.map (Over.homMk
        (Spec.map (CommRingCat.ofHom s.separableClosure.val.toRingHom))
        (geometricPointInclusion_comp K s)).op)⟩ :
      @Scheme.pointSmallEtale _ s.K s.field
        (@IsSepClosed.of_isAlgClosed s.K s.field s.isAlgClosed) s.hom ⟶ etalePoint K s)

/-- The additive comparison from the separable-point stalk to the supplied geometric stalk
is an isomorphism for every abelian étale sheaf. -/
theorem stalkAddCommGrpToGeometricStalk_isIso (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso ((stalkAddCommGrpToGeometricStalk K s).app F) := sorry

end AlgebraicGeometry.Scheme.Etale
