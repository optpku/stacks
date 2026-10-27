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

set_option backward.isDefEq.respectTransparency false in
/-- Changing coefficients commutes with the map on presheaf fibers induced by a map of points. -/
private theorem stalkGaloisModule_fiberCompIso_naturality
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {Φ Ψ : GrothendieckTopology.Point.{u} J} [LocallySmall.{u} C]
    {A B : Type*} [Category* A] [Category* B]
    [Limits.HasColimitsOfSize.{u, u} A] [Limits.HasColimitsOfSize.{u, u} B]
    (T : A ⥤ B) [Limits.PreservesFilteredColimitsOfSize.{u, u} T]
    (f : Φ ⟶ Ψ) (P : Cᵒᵖ ⥤ A) :
    f.presheafFiber.app (P ⋙ T) ≫ (Φ.presheafFiberCompIso T).hom.app P =
      (Ψ.presheafFiberCompIso T).hom.app P ≫ T.map (f.presheafFiber.app P) := by
  apply Ψ.presheafFiber_hom_ext
  intro U x
  simp only [GrothendieckTopology.Point.Hom.presheafFiber_app,
    GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc_assoc,
    GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc,
    GrothendieckTopology.Point.toPresheafFiber_presheafFiberCompIso_hom_app,
    GrothendieckTopology.Point.toPresheafFiber_presheafFiberCompIso_hom_app_assoc, ← T.map_comp]

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
        𝟙 (ModuleCat.of ℤ (stalkAddCommGrp K ⟨point, isAlgClosed⟩ F)) := by
  let s : GeometricPoint (Spec (.of K)) := ⟨point, isAlgClosed⟩
  have hσ : (geometricPointGaloisIso K s 1).hom = 𝟙 _ := by
    apply Over.OverMorphism.ext
    change Spec.map (𝟙 (CommRingCat.of s.separableClosure)) = 𝟙 _
    exact Spec.map_id _
  have hpoint : (⟨geometricPointFiberMap (geometricPointHom K s)
      (geometricPointGaloisIso K s 1)⟩ : etalePoint K s ⟶ etalePoint K s) =
      𝟙 (etalePoint K s) := by
    apply GrothendieckTopology.Point.hom_ext
    simp [geometricPointFiberMap, hσ, etalePoint]
    rfl
  unfold stalkGaloisModuleAction
  rw [hpoint, GrothendieckTopology.Point.Hom.sheafFiber_id]
  rfl

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
  by
    let s : GeometricPoint (Spec (.of K)) := ⟨point, isAlgClosed⟩
    have hστ : (geometricPointGaloisIso K s (σ * τ)).hom =
        (geometricPointGaloisIso K s σ).hom ≫ (geometricPointGaloisIso K s τ).hom := by
      apply Over.OverMorphism.ext
      change Spec.map (CommRingCat.ofHom (σ * τ).toRingHom) =
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.map (CommRingCat.ofHom τ.toRingHom)
      rw [← Spec.map_comp]
      congr 1
    have hpoint : (⟨geometricPointFiberMap (geometricPointHom K s)
        (geometricPointGaloisIso K s (σ * τ))⟩ : etalePoint K s ⟶ etalePoint K s) =
        CategoryStruct.comp (obj := (Spec (.of K)).smallEtaleTopology.Point)
          (⟨geometricPointFiberMap (geometricPointHom K s)
            (geometricPointGaloisIso K s σ)⟩ : etalePoint K s ⟶ etalePoint K s)
          (⟨geometricPointFiberMap (geometricPointHom K s)
            (geometricPointGaloisIso K s τ)⟩ : etalePoint K s ⟶ etalePoint K s) := by
      apply GrothendieckTopology.Point.hom_ext
      simp only [GrothendieckTopology.Point.comp_hom, geometricPointFiberMap, hστ,
        op_comp, Functor.map_comp, Functor.whiskerLeft_comp]
      rfl
    unfold stalkGaloisModuleAction
    rw [hpoint, GrothendieckTopology.Point.Hom.sheafFiber_comp]
    rfl

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

set_option backward.isDefEq.respectTransparency false in
/-- Every element of the additive étale stalk has open stabilizer in the residue-field Galois group. -/
theorem stalkGaloisModuleFromFieldValuedPoint_openStabilizer
    (K : Type u) [Field K] (point : FieldValuedPoint (Spec (.of K)))
    (isAlgClosed : IsAlgClosed point.K)
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :
    openStabilizer ℤ
      Gal(point.separableClosureOfAlgClosed isAlgClosed /
        (Spec (.of K)).residueField point.image)
      (stalkGaloisModuleFromFieldValuedPoint.action K point isAlgClosed F) := by
  let s : GeometricPoint (Spec (.of K)) := ⟨point, isAlgClosed⟩
  let T := CategoryTheory.forget AddCommGrpCat.{u}
  let Fset := (sheafCompose (Spec (.of K)).smallEtaleTopology T).obj F
  let X := stalkGaloisSetAction K s Fset
  let e := ((etalePoint K s).presheafFiberCompIso T).app F.obj
  haveI : X.IsContinuous := stalkGaloisSetAction_continuous K s Fset
  haveI : DiscreteTopology ((forget₂ (Action TopCat s.absoluteGaloisGroup) TopCat).obj X) :=
    inferInstanceAs (DiscreteTopology (TopCat.discrete.obj
      ((etalePoint K s).presheafFiber.obj Fset.obj)))
  intro x
  let y : (forget₂ (Action TopCat s.absoluteGaloisGroup) TopCat).obj X := e.inv x
  have hey : e.hom y = x := ConcreteCategory.congr_hom e.inv_hom_id x
  have hinj : Function.Injective e.hom :=
    ((isIso_iff_bijective e.hom).1 inferInstance).1
  have hstab :
      (MulAction.stabilizer s.absoluteGaloisGroup x : Set s.absoluteGaloisGroup) =
        (MulAction.stabilizer s.absoluteGaloisGroup y : Set s.absoluteGaloisGroup) := by
    ext σ
    change (stalkGaloisModuleAction K s F σ) x = x ↔
      stalkGaloisAction (geometricPointHom K s) (geometricPointGaloisIso K s σ)
        Fset.obj y = y
    have hcomm := ConcreteCategory.congr_hom
      (stalkGaloisModule_fiberCompIso_naturality T
        (⟨geometricPointFiberMap (geometricPointHom K s)
          (geometricPointGaloisIso K s σ)⟩ : etalePoint K s ⟶ etalePoint K s)
        F.obj) y
    change e.hom
        (stalkGaloisAction (geometricPointHom K s) (geometricPointGaloisIso K s σ)
          Fset.obj y) = (stalkGaloisModuleAction K s F σ) (e.hom y) at hcomm
    rw [← hey, ← hcomm]
    exact hinj.eq_iff
  change IsOpen (MulAction.stabilizer s.absoluteGaloisGroup x : Set s.absoluteGaloisGroup)
  rw [hstab]
  exact stabilizer_isOpen s.absoluteGaloisGroup y

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
        (stalkGaloisModuleFromFieldValuedPoint.obj K point isAlgClosed G).obj.ρ σ := by
  ext x
  exact ConcreteCategory.congr_hom
    ((GrothendieckTopology.Point.Hom.sheafFiber
      (⟨geometricPointFiberMap (geometricPointHom K ⟨point, isAlgClosed⟩)
        (geometricPointGaloisIso K ⟨point, isAlgClosed⟩ σ)⟩ :
        etalePoint K ⟨point, isAlgClosed⟩ ⟶ etalePoint K ⟨point, isAlgClosed⟩)
      (A := AddCommGrpCat.{u})).naturality f).symm x

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
      𝟙 (stalkGaloisModuleFromFieldValuedPoint.obj K point isAlgClosed F) := by
  apply ObjectProperty.hom_ext
  apply Action.hom_ext
  ext x
  exact ConcreteCategory.congr_hom
    (((etalePoint K ⟨point, isAlgClosed⟩).sheafFiber
      (A := AddCommGrpCat.{u})).map_id F) x

/-- Additive stalk maps preserve composition of sheaf morphisms. -/
theorem stalkGaloisModuleFromFieldValuedPoint_map_comp
    (K : Type u) [Field K] (point : FieldValuedPoint (Spec (.of K)))
    (isAlgClosed : IsAlgClosed point.K)
    {F G H : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}}
    (f : F ⟶ G) (g : G ⟶ H) :
    stalkGaloisModuleFromFieldValuedPoint.map K point isAlgClosed (f ≫ g) =
      stalkGaloisModuleFromFieldValuedPoint.map K point isAlgClosed f ≫
        stalkGaloisModuleFromFieldValuedPoint.map K point isAlgClosed g := by
  apply ObjectProperty.hom_ext
  apply Action.hom_ext
  ext x
  exact ConcreteCategory.congr_hom
    (((etalePoint K ⟨point, isAlgClosed⟩).sheafFiber
      (A := AddCommGrpCat.{u})).map_comp f g) x

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
      (stalkGaloisModuleFromFieldValuedPoint K point isAlgClosed) := by
  infer_instance

/-- The additive stalk functor at an algebraically closed field-valued point preserves
finite colimits. -/
instance stalkGaloisModuleFromFieldValuedPoint_preservesFiniteColimits
    (K : Type u) [Field K] (point : FieldValuedPoint (Spec (.of K)))
    (isAlgClosed : IsAlgClosed point.K) :
    Limits.PreservesFiniteColimits
      (stalkGaloisModuleFromFieldValuedPoint K point isAlgClosed) := by
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The stalk functor from abelian étale sheaves to discrete continuous Galois modules is
additive at every algebraically closed field-valued point. -/
instance stalkGaloisModuleFromFieldValuedPoint_additive
    (K : Type u) [Field K] (point : FieldValuedPoint (Spec (.of K)))
    (isAlgClosed : IsAlgClosed point.K) :
    (stalkGaloisModuleFromFieldValuedPoint K point isAlgClosed).Additive := by
  haveI : ((etalePoint K ⟨point, isAlgClosed⟩).sheafFiber
      (A := AddCommGrpCat.{u})).Additive :=
    Functor.additive_of_preserves_binary_products _
  constructor
  intro F G f g
  apply ObjectProperty.hom_ext
  apply Action.hom_ext
  ext x
  exact ConcreteCategory.congr_hom
    (((etalePoint K ⟨point, isAlgClosed⟩).sheafFiber
      (A := AddCommGrpCat.{u})).map_add (f := f) (g := g)) x

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

set_option backward.isDefEq.respectTransparency false in
/-- The additive comparison from the separable-point stalk to the supplied geometric stalk
is an isomorphism for every abelian étale sheaf. -/
theorem stalkAddCommGrpToGeometricStalk_isIso (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso ((stalkAddCommGrpToGeometricStalk K s).app F) := by
  let Ψ := @Scheme.pointSmallEtale _ s.K s.field
    (@IsSepClosed.of_isAlgClosed s.K s.field s.isAlgClosed) s.hom
  let f : Ψ ⟶ etalePoint K s :=
    ⟨Functor.whiskerLeft (Etale.forget (Spec (.of K)))
      (coyoneda.map (Over.homMk
        (Spec.map (CommRingCat.ofHom s.separableClosure.val.toRingHom))
        (geometricPointInclusion_comp K s)).op)⟩
  let T := CategoryTheory.forget AddCommGrpCat.{u}
  let Fset := (sheafCompose (Spec (.of K)).smallEtaleTopology T).obj F
  have hbij : Function.Bijective (f.presheafFiber.app (F.obj ⋙ T)) :=
    separableStalkToGeometricStalk_bijective K s Fset
  haveI : IsIso (f.presheafFiber.app (F.obj ⋙ T)) :=
    (isIso_iff_bijective _).2 hbij
  have hsquare := stalkGaloisModule_fiberCompIso_naturality T f F.obj
  haveI : IsIso (((etalePoint K s).presheafFiberCompIso T).hom.app F.obj ≫
      T.map (f.presheafFiber.app F.obj)) := by
    rw [← hsquare]
    infer_instance
  haveI : IsIso (T.map (f.presheafFiber.app F.obj)) :=
    (isIso_comp_left_iff
      (((etalePoint K s).presheafFiberCompIso T).hom.app F.obj)
      (T.map (f.presheafFiber.app F.obj))).1 inferInstance
  change IsIso (f.presheafFiber.app F.obj)
  exact isIso_of_reflects_iso (f.presheafFiber.app F.obj) T

end AlgebraicGeometry.Scheme.Etale
