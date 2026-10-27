/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.TotalComplexShift
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Shift.Localization
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Pullback.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Zero
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings.Triangulated
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Bifunctor
public import ReasLib.AlgebraicTopology.SimplicialObject.Augmentation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.AtiyahExtension
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.SimplicialAugmentation

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.AtiyahSequence
public import ReasLib.CategoryTheory.Localization.FormalIso

/-!
# Atiyah triangle of a sheaf of modules

Applying the augmentation lower shriek `Lπ_! : D(P_•) ⟶ D(B)` of the standard-resolution
augmentation `P_• ⟶ B` to the simplicial first principal-parts sequence produces a distinguished
triangle in `D(B)`, displayed on the vertices `L(φ) ⊗^L F`, `Lπ_!(P¹_{P_•/A}(F))`, and `F`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open ComplexShape
open Opposite
open HomologicalComplex
open AlgebraicTopology
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.CotangentComplex
open scoped Simplicial
open scoped SheafOfModules.RingedSite.CotangentComplex
open CategoryTheory.MonoidalCategory
open CategoryTheory.SimplicialSite

noncomputable section

-- Internal computation maps remain private to the exposed constructions.
set_option backward.privateInPublic true

universe u

namespace SheafOfModules.RingedSite.CotangentComplex

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
variable [UnivLE.{u, u}]
variable [HasSheafify (SimplicialSite.topology J) AddCommGrpCat.{u}]
variable [GrothendieckTopology.WEqualsLocallyBijective
    (SimplicialSite.topology J) AddCommGrpCat.{u}]
variable [GrothendieckTopology.HasSheafCompose (SimplicialSite.topology J)
    (forget₂ CommRingCat.{u} RingCat.{u})]
variable {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
variable (F : ringedSiteModuleCategory.{u, u, u, u} J B)

-- Local instance justification (defeq pin): pin the canonical standard derived category of module sheaves.
attribute [local instance] moduleCategoryHasDerivedCategory
-- Local instance justification (defeq pin): pin the canonical abelian category of module sheaves.
attribute [local instance] moduleCategoryAbelian

variable [DerivedCategory.DerivedTensor.Has (C := ringedSiteModuleCategory.{u, u, u, u} J B)]
variable [DerivedCategory.DerivedTensor.Left.Has (C := ringedSiteModuleCategory.{u, u, u, u} J B)]
variable [DerivedCategory.DerivedTensor.Bifunctor.Has (C := ringedSiteModuleCategory.{u, u, u, u} J B)]

/-- The standard derived-category instance on simplicial diagrams of ringed-site modules. -/
instance simplicialDiagramHasDerivedCategory :
    HasDerivedCategory (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B) :=
  HasDerivedCategory.standard _

/-- Coproducts along total-complex antidiagonals exist in ringed-site modules. -/
instance hasTotal_ringedSite_bicomplex
    (K : HomologicalComplex₂ (ringedSiteModuleCategory.{u, u, u, u} J B)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) :
    K.HasTotal (ComplexShape.up ℤ) :=
  by intro n; infer_instance

private def totalFunctorShiftIso (n : ℤ) :
    shiftFunctor (HomologicalComplex₂ (ringedSiteModuleCategory.{u, u, u, u} J B)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n ⋙
      HomologicalComplex₂.totalFunctor (ringedSiteModuleCategory.{u, u, u, u} J B) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) ≅
    HomologicalComplex₂.totalFunctor (ringedSiteModuleCategory.{u, u, u, u} J B) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
      shiftFunctor (CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J B) ℤ) n :=
  NatIso.ofComponents (fun K => HomologicalComplex₂.totalShift₁Iso (x := n) (K := K))
    (fun f => HomologicalComplex₂.totalShift₁Iso_hom_naturality f n)

/-- Totalization's shift comparisons respect zero and addition of shifts. -/
private theorem totalFunctor_commShift_laws :
    totalFunctorShiftIso (B := B) 0 = Functor.CommShift.isoZero
      (HomologicalComplex₂.totalFunctor (ringedSiteModuleCategory.{u, u, u, u} J B) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ℤ ∧
    ∀ a b : ℤ, totalFunctorShiftIso (B := B) (a + b) =
      Functor.CommShift.isoAdd (totalFunctorShiftIso (B := B) a)
        (totalFunctorShiftIso (B := B) b) := sorry

/-- Totalization commutes with the outer cohomological shift. -/
instance totalFunctor_commShift :
    (HomologicalComplex₂.totalFunctor (ringedSiteModuleCategory.{u, u, u, u} J B) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).CommShift ℤ where
  commShiftIso := totalFunctorShiftIso (B := B)
  commShiftIso_zero := (totalFunctor_commShift_laws (B := B)).1
  commShiftIso_add := (totalFunctor_commShift_laws (B := B)).2

/-- Degreewise underived extension of scalars along the augmentations `P_n → B`. -/
private def extensionMap (X : SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ))
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (extendAlong ((augmentation φ).app n)).obj (evalAtDegree X n) ⟶
      (extendAlong ((augmentation φ).app m)).obj (evalAtDegree X m) :=
  ((extendRestrictAdj ((augmentation φ).app n)).homEquiv _ _).symm
    (evalAtDegreeMap X f ≫
      (restrictionAlong ((standardSimplicial φ).map f)).map
        ((extendRestrictAdj ((augmentation φ).app m)).unit.app (evalAtDegree X m)) ≫
      (SheafOfModules.Restriction.compIso'
          (ringSheafMap ((standardSimplicial φ).map f))
          (ringSheafMap ((augmentation φ).app m))
          (ringSheafMap ((augmentation φ).app n))
          (standardMap_comp_augmentation_ringSheaf A (Under.mk φ) f)).hom.app _)

/-- Degreewise scalar extension respects identities, composition, and module morphisms. -/
private theorem extensionDegreewise_laws :
    (∀ (X : SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ))
      (n : SimplexCategoryᵒᵖ), extensionMap φ X (𝟙 n) = 𝟙 _) ∧
    (∀ (X : SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ))
      {n m k : SimplexCategoryᵒᵖ} (f : n ⟶ m) (g : m ⟶ k),
      extensionMap φ X (f ≫ g) =
        extensionMap φ X (n := n) (m := m) f ≫ extensionMap φ X (n := m) (m := k) g) ∧
    (∀ {X Y : SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ)}
      (α : X ⟶ Y) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m),
      extensionMap φ X (n := n) (m := m) f ≫
          (extendAlong ((augmentation φ).app m)).map (evalAtDegreeHom α m) =
        (extendAlong ((augmentation φ).app n)).map (evalAtDegreeHom α n) ≫
          extensionMap φ Y (n := n) (m := m) f) := sorry

/-- Scalar extension in every simplicial degree, with transitions induced by the augmentation. -/
def extensionDegreewise :
    SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ) ⥤
      (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B) where
  obj X :=
    { obj := fun n ↦ (extendAlong ((augmentation φ).app n)).obj (evalAtDegree X n)
      map := fun {n m} f ↦ extensionMap φ X f
      map_id := (extensionDegreewise_laws φ).1 X
      map_comp := fun f g => (extensionDegreewise_laws φ).2.1 X f g }
  map {X Y} α :=
    { app := fun n ↦ (extendAlong ((augmentation φ).app n)).map (evalAtDegreeHom α n)
      naturality := fun {U V} f => (extensionDegreewise_laws φ).2.2 α f }
  map_id X := by
    apply NatTrans.ext
    funext n
    change (extendAlong ((augmentation φ).app n)).map
      (evalAtDegreeHom (𝟙 X) n) = 𝟙 _
    have h : evalAtDegreeHom (𝟙 X) n = 𝟙 (evalAtDegree X n) := rfl
    rw [h, CategoryTheory.Functor.map_id]
  map_comp {X Y Z} α β := by
    apply NatTrans.ext
    funext n
    change (extendAlong ((augmentation φ).app n)).map
      (evalAtDegreeHom (α ≫ β) n) =
        (extendAlong ((augmentation φ).app n)).map (evalAtDegreeHom α n) ≫
          (extendAlong ((augmentation φ).app n)).map (evalAtDegreeHom β n)
    have h : evalAtDegreeHom (α ≫ β) n = evalAtDegreeHom α n ≫ evalAtDegreeHom β n := rfl
    rw [h, CategoryTheory.Functor.map_comp]

/-- Unfolding of `extensionDegreewise` on objects: degreewise `extendAlong` of `evalAtDegree`. -/
theorem extensionDegreewise_obj_obj
    (X : SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ)) (n : SimplexCategoryᵒᵖ) :
    ((extensionDegreewise φ).obj X).obj n =
      (extendAlong ((augmentation φ).app n)).obj (evalAtDegree X n) :=
  rfl

/-- Degreewise extension of scalars is additive. -/
instance extensionDegreewise_additive : (extensionDegreewise φ).Additive :=
  sorry

private def constantAssemblyMap
    (D : SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B)
    (n m : SimplexCategoryᵒᵖ) (f : n ⟶ m) :
    D.obj n ⟶ (restrictionAlong
      (((SimplicialObject.const (Sheaf J CommRingCat.{u})).obj B).map f)).obj (D.obj m) :=
  D.map f ≫ (SheafOfModules.Restriction.idComponentIso'
    (ringSheafMap (𝟙 B))
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map_id B) (D.obj m)).hom

private def constantAssemblyCoherence : Prop :=
  ∀ D : SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B,
    (∀ (U : (SimplexCategory × C)ᵒᵖ) (t : (D.obj (op U.unop.1)).val.obj (op U.unop.2)),
      (ofDegreewiseMap ((SimplicialObject.const (Sheaf J CommRingCat.{u})).obj B)
        D.obj (constantAssemblyMap D) (𝟙 U)).hom t = t) ∧
    degreewiseMapComp ((SimplicialObject.const (Sheaf J CommRingCat.{u})).obj B)
      D.obj (constantAssemblyMap D)

private def assembledConstant (h : constantAssemblyCoherence (J := J) (B := B))
    (D : SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B) :
    SimplicialSite.ModuleCat.{u, u, u, u} (J := J)
      ((SimplicialObject.const (Sheaf J CommRingCat.{u})).obj B) :=
  ofDegreewise _ D.obj (constantAssemblyMap D) (h D).1 (h D).2

private def assembledEvalHomComponent (h : constantAssemblyCoherence (J := J) (B := B))
    (D : SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B) (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) :
    (evalAtDegree (assembledConstant h D) n).val.obj U ⟶ (D.obj n).val.obj U :=
  _root_.ModuleCat.homMk (𝟙 _) (by intro r; ext t; rfl)

private def assembledEvalInvComponent (h : constantAssemblyCoherence (J := J) (B := B))
    (D : SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B) (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) :
    (D.obj n).val.obj U ⟶ (evalAtDegree (assembledConstant h D) n).val.obj U :=
  _root_.ModuleCat.homMk (𝟙 _) (by intro r; ext t; rfl)

private def extensionUnitComponent (h : constantAssemblyCoherence (J := J) (B := B))
    (X : SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ))
    (U : (SimplexCategory × C)ᵒᵖ) :
    X.val.obj U ⟶
      ((restrictionAlong (SimplicialSite.ringSheafMap (augmentation φ))).obj
        (assembledConstant h ((extensionDegreewise φ).obj X))).val.obj U :=
  (((extendRestrictAdj ((augmentation φ).app (op U.unop.1))).unit.app
    (evalAtDegree X (op U.unop.1))).val.app (op U.unop.2))

private def extensionAssemblyNaturality
    (h : constantAssemblyCoherence (J := J) (B := B)) : Prop :=
    (∀ (D : SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B) (n : SimplexCategoryᵒᵖ)
      {U V : Cᵒᵖ} (f : U ⟶ V),
      (evalAtDegree (assembledConstant h D) n).val.map f ≫
          (_root_.ModuleCat.restrictScalars _).map (assembledEvalHomComponent h D n V) =
        assembledEvalHomComponent h D n U ≫ (D.obj n).val.map f) ∧
    (∀ (D : SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B) (n : SimplexCategoryᵒᵖ)
      {U V : Cᵒᵖ} (f : U ⟶ V),
      (D.obj n).val.map f ≫
          (_root_.ModuleCat.restrictScalars _).map (assembledEvalInvComponent h D n V) =
        assembledEvalInvComponent h D n U ≫ (evalAtDegree (assembledConstant h D) n).val.map f) ∧
    (∀ (X : SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ))
      {U V : (SimplexCategory × C)ᵒᵖ} (f : U ⟶ V),
      X.val.map f ≫ (_root_.ModuleCat.restrictScalars _).map (extensionUnitComponent φ h X V) =
        extensionUnitComponent φ h X U ≫
          ((restrictionAlong (SimplicialSite.ringSheafMap (augmentation φ))).obj
            (assembledConstant h ((extensionDegreewise φ).obj X))).val.map f)

private def assembledEvalHom (h : constantAssemblyCoherence (J := J) (B := B))
    (k : extensionAssemblyNaturality φ h)
    (D : SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B) (n : SimplexCategoryᵒᵖ) :
    evalAtDegree (assembledConstant h D) n ⟶ D.obj n where
  val := { app := assembledEvalHomComponent h D n
           naturality := fun {U V} f => k.1 D n f }

private def extensionUnitAssembly (h : constantAssemblyCoherence (J := J) (B := B))
    (k : extensionAssemblyNaturality φ h)
    (X : SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ)) :
    X ⟶ (restrictionAlong (SimplicialSite.ringSheafMap (augmentation φ))).obj
      (assembledConstant h ((extensionDegreewise φ).obj X)) where
  val := { app := extensionUnitComponent φ h X
           naturality := fun {U V} f => k.2.2 X f }

private def extensionProductToAssembly (h : constantAssemblyCoherence (J := J) (B := B))
    (k : extensionAssemblyNaturality φ h)
    (X : SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ)) :
    (extendAlong (SimplicialSite.ringSheafMap (augmentation φ))).obj X ⟶
      assembledConstant h ((extensionDegreewise φ).obj X) :=
  ((extendRestrictAdj (SimplicialSite.ringSheafMap (augmentation φ))).homEquiv _ _).symm
    (extensionUnitAssembly φ h k X)

private def extensionDegreewiseIsoHomComponent
    (h : constantAssemblyCoherence (J := J) (B := B)) (k : extensionAssemblyNaturality φ h)
    (X : SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ)) (n : SimplexCategoryᵒᵖ) :
    ((extendAlong (SimplicialSite.ringSheafMap (augmentation φ)) ⋙
      constantModuleDiagram B).obj X).obj n ⟶ ((extensionDegreewise φ).obj X).obj n :=
  evalAtDegreeHom (extensionProductToAssembly φ h k X) n ≫
    assembledEvalHom φ h k ((extensionDegreewise φ).obj X) n

private def extensionDegreewiseIsoInvComponent
    (X : SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ)) (n : SimplexCategoryᵒᵖ) :
    ((extensionDegreewise φ).obj X).obj n ⟶
      ((extendAlong (SimplicialSite.ringSheafMap (augmentation φ)) ⋙
        constantModuleDiagram B).obj X).obj n :=
  ((extendRestrictAdj ((augmentation φ).app n)).homEquiv _ _).symm
    (evalAtDegreeHom
      ((extendRestrictAdj (SimplicialSite.ringSheafMap (augmentation φ))).unit.app X) n)

private def extensionDegreewiseIsoCoherence
    (h : constantAssemblyCoherence (J := J) (B := B)) (k : extensionAssemblyNaturality φ h) : Prop :=
  let E := extendAlong (SimplicialSite.ringSheafMap (augmentation φ)) ⋙ constantModuleDiagram B
  (∀ (X : SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ))
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m),
    (E.obj X).map f ≫ extensionDegreewiseIsoHomComponent φ h k X m =
      extensionDegreewiseIsoHomComponent φ h k X n ≫ ((extensionDegreewise φ).obj X).map f) ∧
  (∀ (X : SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ))
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m),
    ((extensionDegreewise φ).obj X).map f ≫ extensionDegreewiseIsoInvComponent φ X m =
      extensionDegreewiseIsoInvComponent φ X n ≫ (E.obj X).map f) ∧
  (∀ {X Y : SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ)} (α : X ⟶ Y) n,
    (E.map α).app n ≫ extensionDegreewiseIsoHomComponent φ h k Y n =
      extensionDegreewiseIsoHomComponent φ h k X n ≫ ((extensionDegreewise φ).map α).app n) ∧
  (∀ (X : SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ)) n,
    extensionDegreewiseIsoHomComponent φ h k X n ≫ extensionDegreewiseIsoInvComponent φ X n = 𝟙 _) ∧
  (∀ (X : SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ)) n,
    extensionDegreewiseIsoInvComponent φ X n ≫ extensionDegreewiseIsoHomComponent φ h k X n = 𝟙 _)

/-- Evaluation commutes with scalar extension, with comparisons induced by the two scalar adjunctions. -/
private theorem extensionDegreewiseIso_laws :
    constantAssemblyCoherence (J := J) (B := B) ∧
    ∀ h : constantAssemblyCoherence (J := J) (B := B),
      extensionAssemblyNaturality φ h ∧
      ∀ k : extensionAssemblyNaturality φ h, extensionDegreewiseIsoCoherence φ h k := sorry

/-- Scalar extension on the simplicial site agrees with scalar extension in every degree. -/
def extensionDegreewiseIso :
    extendAlong (SimplicialSite.ringSheafMap (augmentation φ)) ⋙ constantModuleDiagram B ≅
      extensionDegreewise φ :=
  let h := (extensionDegreewiseIso_laws φ).1
  let k := ((extensionDegreewiseIso_laws φ).2 h).1
  let l := ((extensionDegreewiseIso_laws φ).2 h).2 k
  NatIso.ofComponents
    (fun X =>
      { hom := { app := extensionDegreewiseIsoHomComponent φ h k X
                 naturality := fun {U V} f => l.1 X f }
        inv := { app := extensionDegreewiseIsoInvComponent φ X
                 naturality := fun {U V} f => l.2.1 X f }
        hom_inv_id := by apply NatTrans.ext; funext n; exact l.2.2.2.1 X n
        inv_hom_id := by apply NatTrans.ext; funext n; exact l.2.2.2.2 X n })
    (fun α => by apply NatTrans.ext; funext n; exact l.2.2.1 α n)

/-- Derived scalar extension on the simplicial site, followed by exact degree evaluation. -/
def derivedExtension :
    RingedSite.Hom.ModuleDerived
        (RingedSite.ofCommRingSheaf (SimplicialSite.topology J)
          (SimplicialSite.ringSheaf (standardSimplicial φ))) ⥤
      DerivedCategory (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B) :=
  SameSite.pullbackDerived (SimplicialSite.ringSheafMap (augmentation φ)) ⋙
    constantModuleDiagramDerived B

/-- Derived scalar extension commutes with integer shifts. -/
instance derivedExtension_commShift : (derivedExtension φ).CommShift ℤ :=
  Functor.CommShift.comp
    (SameSite.pullbackDerived (SimplicialSite.ringSheafMap (augmentation φ)))
    ((constantModuleDiagram B).mapDerivedCategory)

/-- The Moore cochain complex of a simplicial `B`-module sheaf. -/
def mooreExtend :
    (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B) ⥤
      CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J B) ℤ :=
  alternatingFaceMapComplex (ringedSiteModuleCategory.{u, u, u, u} J B) ⋙
    ComplexShape.embeddingDownNat.extendFunctor (ringedSiteModuleCategory.{u, u, u, u} J B)

/-- Moore evaluation is additive. -/
instance mooreExtend_additive : (mooreExtend (B := B)).Additive :=
  sorry

/-- The total-complex shape sends `(0, n)` to `n`. -/
private theorem π_up_zero (n : ℤ) :
    ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (0, n) = n :=
  sorry

/-- Inclusion of the degree-zero row into the total complex of a single bicomplex. -/
private def totalSingleι (K : CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J B) ℤ) (n : ℤ) :
    K.X n ⟶
      (HomologicalComplex₂.total
        ((HomologicalComplex.single (CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J B) ℤ)
            (ComplexShape.up ℤ) 0).obj K)
        (ComplexShape.up ℤ)).X n :=
  HomologicalComplex₂.ιTotal
    ((HomologicalComplex.single (CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J B) ℤ)
        (ComplexShape.up ℤ) 0).obj K)
    (ComplexShape.up ℤ) 0 n n (π_up_zero n)

/-- The `(i₁, i₂)`-summand of a degree-zero single bicomplex in degree `n` identifies with
`K.X n` when `i₁ = 0`. -/
private theorem totalSingle_component_eq (K : CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J B) ℤ)
    (n i₁ i₂ : ℤ) (h : i₁ = 0)
    (hi : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (i₁, i₂) = n) :
    (((HomologicalComplex.single (CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J B) ℤ)
        (ComplexShape.up ℤ) 0).obj K).X i₁).X i₂ =
      K.X n :=
  sorry

/-- Projection from the total complex of a degree-zero single bicomplex onto the original
complex in degree `n`. -/
private def totalSingleπ (K : CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J B) ℤ) (n : ℤ) :
    (HomologicalComplex₂.total
        ((HomologicalComplex.single (CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J B) ℤ)
            (ComplexShape.up ℤ) 0).obj K)
        (ComplexShape.up ℤ)).X n ⟶ K.X n :=
  HomologicalComplex₂.totalDesc
    ((HomologicalComplex.single (CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J B) ℤ)
        (ComplexShape.up ℤ) 0).obj K)
    (fun i₁ i₂ hi =>
      dite (i₁ = 0)
        (fun h => eqToHom (totalSingle_component_eq K n i₁ i₂ h hi))
        (fun _ => 0))

/-- The single-row inclusion and projection are mutually inverse and respect differentials. -/
private theorem totalSingleIso_laws (K : CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J B) ℤ) :
    (∀ n, totalSingleπ K n ≫ totalSingleι K n = 𝟙 _) ∧
    (∀ n, totalSingleι K n ≫ totalSingleπ K n = 𝟙 _) ∧
    (∀ n m, (HomologicalComplex₂.total
        ((HomologicalComplex.single (CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J B) ℤ)
          (ComplexShape.up ℤ) 0).obj K) (ComplexShape.up ℤ)).d n m ≫ totalSingleπ K m =
      totalSingleπ K n ≫ K.d n m) := sorry

/-- Totalization of a degree-zero single bicomplex recovers the original complex. -/
private def totalSingleIso (K : CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J B) ℤ) :
    HomologicalComplex₂.total
        ((HomologicalComplex.single (CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J B) ℤ)
            (ComplexShape.up ℤ) 0).obj K)
        (ComplexShape.up ℤ) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n =>
      { hom := totalSingleπ K n
        inv := totalSingleι K n
        hom_inv_id := (totalSingleIso_laws K).1 n
        inv_hom_id := (totalSingleIso_laws K).2.1 n })
    (fun n m _ => ((totalSingleIso_laws K).2.2 n m).symm)

/-- Degreewise Moore evaluation of a complex of simplicial `B`-modules, then totalization. -/
def evaluationOnComplex :
    CochainComplex (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B) ℤ ⥤
      DerivedCategory (ringedSiteModuleCategory.{u, u, u, u} J B) :=
  (mooreExtend (B := B)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex₂.totalFunctor (ringedSiteModuleCategory.{u, u, u, u} J B) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q

/-- Moore totalization inverts quasi-isomorphisms of complexes of simplicial modules. -/
theorem evaluationOnComplex_inverts :
    (HomologicalComplex.quasiIso (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B)
        (ComplexShape.up ℤ)).IsInvertedBy
      (evaluationOnComplex (B := B)) := by
  intro K L f hf
  let T := (mooreExtend (B := B)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex₂.totalFunctor (ringedSiteModuleCategory.{u, u, u, u} J B) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  have hq : HomologicalComplex.quasiIso (ringedSiteModuleCategory.{u, u, u, u} J B)
      (ComplexShape.up ℤ) (T.map f) := by sorry
  exact (Localization.formalIso
    (HomologicalComplex.quasiIso (ringedSiteModuleCategory.{u, u, u, u} J B) (ComplexShape.up ℤ))
    DerivedCategory.Q (T.map f) hq).isIso_hom

/-- Evaluation of a simplicial module sheaf by Moore totalization on the derived category. -/
def evaluation :
    DerivedCategory (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B) ⥤
      DerivedCategory (ringedSiteModuleCategory.{u, u, u, u} J B) :=
  CategoryTheory.Localization.lift
    (evaluationOnComplex (B := B)) (evaluationOnComplex_inverts (B := B))
    (DerivedCategory.Q :
      CochainComplex (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B) ℤ ⥤
        DerivedCategory (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B))

/-- Moore totalization of a complex of simplicial modules commutes with integer shifts. -/
instance evaluationOnComplex_commShift :
    (evaluationOnComplex (B := B)).CommShift ℤ :=
  inferInstanceAs
    (((mooreExtend (B := B)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex₂.totalFunctor (ringedSiteModuleCategory.{u, u, u, u} J B) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q).CommShift ℤ)

/-- Derived evaluation is the localization lift of Moore totalization. -/
instance evaluation_lifting :
    Localization.Lifting
      (DerivedCategory.Q :
        CochainComplex (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B) ℤ ⥤
          DerivedCategory (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B))
      (HomologicalComplex.quasiIso (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B)
        (ComplexShape.up ℤ))
      (evaluationOnComplex (B := B)) (evaluation (B := B)) :=
  Localization.liftingLift (evaluationOnComplex (B := B))
    (evaluationOnComplex_inverts (B := B))
    (DerivedCategory.Q :
      CochainComplex (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B) ℤ ⥤
        DerivedCategory (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B))

/-- Derived evaluation commutes with integer shifts. -/
instance evaluation_commShift : (evaluation (B := B)).CommShift ℤ :=
  Functor.commShiftOfLocalization
    (DerivedCategory.Q :
      CochainComplex (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B) ℤ ⥤
        DerivedCategory (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B))
    (HomologicalComplex.quasiIso (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B)
      (ComplexShape.up ℤ))
    ℤ (evaluationOnComplex (B := B)) (evaluation (B := B))

/-- Comparison `L(colim)(single N) ≅ Q(Moore N)` realized as Moore totalization of a single. -/
def evaluationSingleIso
    (N : SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B) :
    (evaluation (B := B)).obj
        ((DerivedCategory.singleFunctor
            (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B) 0).obj N) ≅
      DerivedCategory.Q.obj ((mooreExtend (B := B)).obj N) :=
  (evaluation (B := B)).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ
          (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B) 0).app N) ≪≫
    (CategoryTheory.Localization.fac (evaluationOnComplex (B := B))
        (evaluationOnComplex_inverts (B := B))
        (DerivedCategory.Q :
          CochainComplex (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B) ℤ ⥤
            DerivedCategory (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B))).app
      ((HomologicalComplex.single (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B)
          (ComplexShape.up ℤ) 0).obj N) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex₂.totalFunctor (ringedSiteModuleCategory.{u, u, u, u} J B) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex (mooreExtend (B := B))
            (ComplexShape.up ℤ) 0).app N)) ≪≫
    DerivedCategory.Q.mapIso (totalSingleIso ((mooreExtend (B := B)).obj N))

/-- Computational Moore-evaluation model of the augmentation lower shriek. -/
def computationalLowerShriek :
    RingedSite.Hom.ModuleDerived
        (RingedSite.ofCommRingSheaf (SimplicialSite.topology J)
          (SimplicialSite.ringSheaf (standardSimplicial φ))) ⥤
      RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J B) :=
  derivedExtension φ ⋙ evaluation (B := B)

/-- The derived lower shriek `Lπ_! : D(P_•) ⟶ D(B)` of the standard-resolution augmentation,
as the Moore-evaluation model obtained by derived extension of scalars along `P_• ⟶ B`
followed by Moore evaluation. -/
abbrev atiyahLowerShriek :
    RingedSite.Hom.ModuleDerived
        (RingedSite.ofCommRingSheaf (SimplicialSite.topology J)
          (SimplicialSite.ringSheaf (standardSimplicial φ))) ⥤
      RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J B) :=
  computationalLowerShriek φ

/-- The Moore model of derived augmentation lower shriek agrees with the canonical site construction. -/
theorem atiyahLowerShriek_isomorphic
    [Functor.IsRightAdjoint
      (siteAbelianInverseImageDerived (SimplicialSite.topology J) J SimplicialSite.projection)]
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Cocontinuous.moduleLowerShriek.toDerived
        (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
        (ringSheaf J B))
      (RingedSite.Hom.ModuleQis
        (RingedSite.Cocontinuous.moduleInverseImage.source
          (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
          (ringSheaf J B)))] :
    IsIsomorphic (atiyahLowerShriek φ)
      (SimplicialSite.Derived.augmentationLowerShriek (augmentation φ)) := sorry

/-- Derived lower shriek commutes with integer shifts. -/
instance computationalLowerShriek_commShift : (computationalLowerShriek φ).CommShift ℤ :=
  inferInstanceAs ((derivedExtension φ ⋙ evaluation (B := B)).CommShift ℤ)

private def simplicialPullbackSingle
    (X : SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ)) :
    (SameSite.pullbackDerived (SimplicialSite.ringSheafMap (augmentation φ))).obj
      ((DerivedCategory.singleFunctor
        (SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ)) 0).obj X) ⟶
    (DerivedCategory.singleFunctor
      (SimplicialSite.ModuleCat.{u, u, u, u} (J := J)
        ((SimplicialObject.const (Sheaf J CommRingCat.{u})).obj B)) 0).obj
      ((extendAlong (SimplicialSite.ringSheafMap (augmentation φ))).obj X) :=
  ((RingedSite.Hom.modulePullbackToDerived
      (sameSiteHom (SimplicialSite.ringSheafMap (augmentation φ)))).totalLeftDerivedCounit
    (RingedSite.Hom.moduleLocalization
      (RingedSite.ofCommRingSheaf (SimplicialSite.topology J)
        (SimplicialSite.ringSheaf (standardSimplicial φ))))
    (RingedSite.Hom.ModuleQis
      (RingedSite.ofCommRingSheaf (SimplicialSite.topology J)
        (SimplicialSite.ringSheaf (standardSimplicial φ))))).app
    ((HomotopyCategory.singleFunctor
      (SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ)) 0).obj X) ≫
  (Functor.Homotopy.singleIso
    (RingedSite.Hom.modulePullback
      (sameSiteHom (SimplicialSite.ringSheafMap (augmentation φ)))) 0).hom.app X ≫
  (DerivedCategory.singleFunctor
    (SimplicialSite.ModuleCat.{u, u, u, u} (J := J)
      ((SimplicialObject.const (Sheaf J CommRingCat.{u})).obj B)) 0).map
    ((pullbackExtendIso (SimplicialSite.ringSheafMap (augmentation φ))).hom.app X)

/-- The derived scalar-extension counit on a single module, transported to degreewise extension. -/
def derivedExtensionSingle
    (X : SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ)) :
    (derivedExtension φ).obj
        ((DerivedCategory.singleFunctor
            (SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ)) 0).obj X) ⟶
      (DerivedCategory.singleFunctor
          (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B) 0).obj
        ((extensionDegreewise φ).obj X) :=
  (constantModuleDiagramDerived B).map (simplicialPullbackSingle φ X) ≫
    (constantModuleDiagramSingleIso B).hom.app
      ((extendAlong (SimplicialSite.ringSheafMap (augmentation φ))).obj X) ≫
    (DerivedCategory.singleFunctor
      (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B) 0).map
      ((extensionDegreewiseIso φ).hom.app X)

/-- After totalization, the cotangent counit has a quasi-isomorphism representative.
This uses the standard augmentation and the homology comparison for the standard augmentation;
it does not assert degreewise acyclicity of `Ω ⊗ F`. -/
private theorem cotangentComparison_quasiIso :
    HomotopyCategory.quasiIso (ringedSiteModuleCategory.{u, u, u, u} J B) (ComplexShape.up ℤ)
      (Localization.arrowRepresentative DerivedCategory.Qh ((evaluation (B := B)).map
        (derivedExtensionSingle φ (cotangentModule φ F)))).hom :=
  sorry

/-- The totalized constant-module comparison is a quasi-isomorphism on its actual
homotopy representative. No arbitrary simplicial-site module is asserted acyclic. -/
private theorem restrictedComparison_quasiIso :
    HomotopyCategory.quasiIso (ringedSiteModuleCategory.{u, u, u, u} J B) (ComplexShape.up ℤ)
      (Localization.arrowRepresentative DerivedCategory.Qh ((evaluation (B := B)).map
        (derivedExtensionSingle φ (restrictedModule φ F)))).hom :=
  sorry

/-- Inverse of the specified totalized cotangent comparison, as the formal localization
inverse of its homotopy representative. -/
private def cotangentComparisonInv :=
  (Localization.formalIsoOfArrowRepresentative
    (HomotopyCategory.quasiIso (ringedSiteModuleCategory.{u, u, u, u} J B) (ComplexShape.up ℤ))
    DerivedCategory.Qh _
    (cotangentComparison_quasiIso φ F)).inv

/-- Inverse of the specified totalized constant-module comparison, as the formal localization
inverse of its homotopy representative. -/
private def restrictedComparisonInv :=
  (Localization.formalIsoOfArrowRepresentative
    (HomotopyCategory.quasiIso (ringedSiteModuleCategory.{u, u, u, u} J B) (ComplexShape.up ℤ))
    DerivedCategory.Qh _
    (restrictedComparison_quasiIso φ F)).inv

/-- The formal cotangent inverse is a right inverse to the actual evaluated counit. -/
private theorem cotangentComparison_hom_inv_id :
    (evaluation (B := B)).map (derivedExtensionSingle φ (cotangentModule φ F)) ≫
      cotangentComparisonInv φ F = 𝟙 _ :=
  sorry

/-- The formal cotangent inverse is a left inverse to the actual evaluated counit. -/
private theorem cotangentComparison_inv_hom_id :
    cotangentComparisonInv φ F ≫
      (evaluation (B := B)).map (derivedExtensionSingle φ (cotangentModule φ F)) = 𝟙 _ :=
  sorry

/-- The formal constant-module inverse is a right inverse to the specified comparison. -/
private theorem restrictedComparison_hom_inv_id :
    (evaluation (B := B)).map (derivedExtensionSingle φ (restrictedModule φ F)) ≫
      restrictedComparisonInv φ F = 𝟙 _ :=
  sorry

/-- The formal constant-module inverse is a left inverse to the specified comparison. -/
private theorem restrictedComparison_inv_hom_id :
    restrictedComparisonInv φ F ≫
      (evaluation (B := B)).map (derivedExtensionSingle φ (restrictedModule φ F)) = 𝟙 _ :=
  sorry

/-- The evaluated cotangent counit is invertible with its specified formal inverse. -/
instance derivedExtensionSingle_cotangent_isIso :
    IsIso ((evaluation (B := B)).map (derivedExtensionSingle φ (cotangentModule φ F))) :=
  ({ hom := (evaluation (B := B)).map (derivedExtensionSingle φ (cotangentModule φ F))
     inv := cotangentComparisonInv φ F
     hom_inv_id := cotangentComparison_hom_inv_id φ F
     inv_hom_id := cotangentComparison_inv_hom_id φ F } : _ ≅ _).isIso_hom

/-- The evaluated restricted-module counit is invertible with its specified formal inverse. -/
instance derivedExtensionSingle_restricted_isIso :
    IsIso ((evaluation (B := B)).map (derivedExtensionSingle φ (restrictedModule φ F))) :=
  ({ hom := (evaluation (B := B)).map (derivedExtensionSingle φ (restrictedModule φ F))
     inv := restrictedComparisonInv φ F
     hom_inv_id := restrictedComparison_hom_inv_id φ F
     inv_hom_id := restrictedComparison_inv_hom_id φ F } : _ ≅ _).isIso_hom

/-- The constant simplicial `B`-module with value `F`. -/
def simplicialConstant :
    SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B :=
  (Functor.const _).obj F

/-- Unfolding of `simplicialConstant`. -/
theorem simplicialConstant_obj (n : SimplexCategoryᵒᵖ) :
    (simplicialConstant F).obj n = F :=
  rfl

/-- Tensoring the standard cotangent diagram by a fixed module respects its functor laws. -/
private theorem simplicialCotangent_laws :
    (∀ n : SimplexCategoryᵒᵖ,
      moduleTensorMap ((simplicialModule A (Under.mk φ)).map (𝟙 n)) (𝟙 F) = 𝟙 _) ∧
    (∀ {n m k : SimplexCategoryᵒᵖ} (f : n ⟶ m) (g : m ⟶ k),
      moduleTensorMap ((simplicialModule A (Under.mk φ)).map (f ≫ g)) (𝟙 F) =
        moduleTensorMap ((simplicialModule A (Under.mk φ)).map f) (𝟙 F) ≫
          moduleTensorMap ((simplicialModule A (Under.mk φ)).map g) (𝟙 F)) := sorry

/-- The standard cotangent simplicial module tensored degreewise with a fixed module. -/
def simplicialCotangent :
    SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B where
  obj n := moduleTensor ((simplicialModule A (Under.mk φ)).obj n) F
  map f := moduleTensorMap ((simplicialModule A (Under.mk φ)).map f) (𝟙 F)
  map_id := (simplicialCotangent_laws φ F).1
  map_comp := fun f g => (simplicialCotangent_laws φ F).2 f g

/-- Degreewise, `simplicialCotangent` is the base change of `Ω_{P_n/A}` tensored with `F`. -/
theorem simplicialCotangent_obj (n : SimplexCategoryᵒᵖ) :
    (simplicialCotangent φ F).obj n =
      moduleTensor ((simplicialModule A (Under.mk φ)).obj n) F :=
  rfl

/-- The cochain complex of `B`-modules obtained from `simplicialCotangent`. -/
def tensorModuleCochain : CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J B) ℤ :=
  (mooreExtend (B := B)).obj (simplicialCotangent φ F)

private def evalAtDegreeToRestrictedComponent (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) :
    (evalAtDegree (restrictedModule φ F) n).val.obj U ⟶ ((restrictionAlong ((augmentation φ).app n)).obj F).val.obj U :=
  _root_.ModuleCat.homMk (𝟙 _) (by intro r; ext t; rfl)

/-- The identity on sections commutes with the site restriction maps. -/
private theorem evalAtDegreeToRestricted_laws (n : SimplexCategoryᵒᵖ)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (evalAtDegree (restrictedModule φ F) n).val.map f ≫
        (_root_.ModuleCat.restrictScalars _).map (evalAtDegreeToRestrictedComponent φ F n V) =
      evalAtDegreeToRestrictedComponent φ F n U ≫ ((restrictionAlong ((augmentation φ).app n)).obj F).val.map f := sorry

/-- The identity on sections identifies degree evaluation with its specified coefficient module. -/
private def evalAtDegreeToRestricted (n : SimplexCategoryᵒᵖ) :
    evalAtDegree (restrictedModule φ F) n ⟶ (restrictionAlong ((augmentation φ).app n)).obj F where
  val :=
    { app := evalAtDegreeToRestrictedComponent φ F n
      naturality := fun {U V} f => evalAtDegreeToRestricted_laws φ F n f }

private def restrictedExtendCounitComponent (n : SimplexCategoryᵒᵖ) :
    ((extensionDegreewise φ).obj (restrictedModule φ F)).obj n ⟶ (simplicialConstant F).obj n :=
  ((extendRestrictAdj ((augmentation φ).app n)).homEquiv
        (evalAtDegree (restrictedModule φ F) n) F).symm
      (evalAtDegreeToRestricted φ F n)

/-- The degreewise scalar comparison commutes with simplicial operators. -/
private theorem restrictedExtendCounit_naturality {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    ((extensionDegreewise φ).obj (restrictedModule φ F)).map f ≫ restrictedExtendCounitComponent φ F m =
      restrictedExtendCounitComponent φ F n ≫ (simplicialConstant F).map f := sorry

/-- The counit `B ⊗_{P_n} F ⟶ F` of extension of scalars, as a simplicial map. -/
def restrictedExtendCounit :
    (extensionDegreewise φ).obj (restrictedModule φ F) ⟶ simplicialConstant F where
  app := restrictedExtendCounitComponent φ F
  naturality := fun {U V} f => restrictedExtendCounit_naturality φ F f

private def evalAtDegreeFromRestrictedComponent (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) :
    ((restrictionAlong ((augmentation φ).app n)).obj F).val.obj U ⟶ (evalAtDegree (restrictedModule φ F) n).val.obj U :=
  _root_.ModuleCat.homMk (𝟙 _) (by intro r; ext t; rfl)

/-- The identity on sections commutes with the site restriction maps. -/
private theorem evalAtDegreeFromRestricted_laws (n : SimplexCategoryᵒᵖ)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    ((restrictionAlong ((augmentation φ).app n)).obj F).val.map f ≫
        (_root_.ModuleCat.restrictScalars _).map (evalAtDegreeFromRestrictedComponent φ F n V) =
      evalAtDegreeFromRestrictedComponent φ F n U ≫ (evalAtDegree (restrictedModule φ F) n).val.map f := sorry

/-- The identity on sections identifies degree evaluation with its specified coefficient module. -/
private def evalAtDegreeFromRestricted (n : SimplexCategoryᵒᵖ) :
    (restrictionAlong ((augmentation φ).app n)).obj F ⟶ evalAtDegree (restrictedModule φ F) n where
  val :=
    { app := evalAtDegreeFromRestrictedComponent φ F n
      naturality := fun {U V} f => evalAtDegreeFromRestricted_laws φ F n f }

/-- The target-linear unit along a standard augmentation sends a section to its tensor with one. -/
private def extendRestrictUnit (n : SimplexCategoryᵒᵖ) (G : ringedSiteModuleCategory.{u, u, u, u} J B) :
    G ⟶ (extendAlong ((augmentation φ).app n)).obj
      ((restrictionAlong ((augmentation φ).app n)).obj G) where
  val := (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      (J := J) (ringSheafMap ((augmentation φ).app n)).hom
      ((extendAlong ((augmentation φ).app n)).obj
        ((restrictionAlong ((augmentation φ).app n)).obj G)).isSheaf).symm
    (((extendRestrictAdj ((augmentation φ).app n)).unit.app
      ((restrictionAlong ((augmentation φ).app n)).obj G)).val)

/-- The target-linear unit has the same section map as the scalar adjunction unit. -/
private theorem extendRestrictUnit_apply (n : SimplexCategoryᵒᵖ)
    (G : ringedSiteModuleCategory.{u, u, u, u} J B) (U : Cᵒᵖ) (t : G.val.obj U) :
    ((extendRestrictUnit φ n G).val.app U).hom t =
      (((extendRestrictAdj ((augmentation φ).app n)).unit.app
        ((restrictionAlong ((augmentation φ).app n)).obj G)).val.app U).hom t := rfl

private def restrictedExtendUnitComponent (n : SimplexCategoryᵒᵖ) :
    (simplicialConstant F).obj n ⟶ ((extensionDegreewise φ).obj (restrictedModule φ F)).obj n :=
  extendRestrictUnit φ n F ≫
      (extendAlong ((augmentation φ).app n)).map (evalAtDegreeFromRestricted φ F n)

/-- The degreewise scalar comparison commutes with simplicial operators. -/
private theorem restrictedExtendUnit_naturality {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (simplicialConstant F).map f ≫ restrictedExtendUnitComponent φ F m =
      restrictedExtendUnitComponent φ F n ≫ ((extensionDegreewise φ).obj (restrictedModule φ F)).map f := sorry

/-- The inverse comparison `F ⟶ B ⊗_{P_n} F`, as a simplicial map. -/
def restrictedExtendUnit :
    simplicialConstant F ⟶ (extensionDegreewise φ).obj (restrictedModule φ F) where
  app := restrictedExtendUnitComponent φ F
  naturality := fun {U V} f => restrictedExtendUnit_naturality φ F f

private def evalAtDegree_cotangentModuleComponent (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) :
    (evalAtDegree (cotangentModule φ F) n).val.obj U ⟶ ((degreeSequence φ F n).X₁).val.obj U :=
  _root_.ModuleCat.homMk (𝟙 _) (by intro r; ext t; rfl)

/-- The identity on sections commutes with the site restriction maps. -/
private theorem evalAtDegree_cotangentModule_laws (n : SimplexCategoryᵒᵖ)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (evalAtDegree (cotangentModule φ F) n).val.map f ≫
        (_root_.ModuleCat.restrictScalars _).map (evalAtDegree_cotangentModuleComponent φ F n V) =
      evalAtDegree_cotangentModuleComponent φ F n U ≫ ((degreeSequence φ F n).X₁).val.map f := sorry

/-- The identity on sections identifies degree evaluation with its specified coefficient module. -/
private def evalAtDegree_cotangentModule (n : SimplexCategoryᵒᵖ) :
    evalAtDegree (cotangentModule φ F) n ⟶ (degreeSequence φ F n).X₁ where
  val :=
    { app := evalAtDegree_cotangentModuleComponent φ F n
      naturality := fun {U V} f => evalAtDegree_cotangentModule_laws φ F n f }

/-- `evalAtDegree_cotangentModule` is the identity on underlying sections. -/
private theorem evalAtDegree_cotangentModule_apply (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ)
    (t : (evalAtDegree (cotangentModule φ F) n).val.obj U) :
    ((evalAtDegree_cotangentModule φ F n).val.app U).hom t = t :=
  rfl

/-- Degreewise associativity
`B ⊗_{P_n} (Ω_{P_n/A} ⊗_{P_n} F) ⟶ (Ω_{P_n/A} ⊗_{P_n} B) ⊗_B F`. -/
def cotangentExtendDegree (n : SimplexCategoryᵒᵖ) :
    ((extensionDegreewise φ).obj (cotangentModule φ F)).obj n ⟶
      (simplicialCotangent φ F).obj n :=
  (extendAlong ((augmentation φ).app n)).map (evalAtDegree_cotangentModule φ F n) ≫
    ((extendRestrictAdj ((augmentation φ).app n)).homEquiv
        (degreeSequence φ F n).X₁
        (moduleTensor ((simplicialModule A (Under.mk φ)).obj n) F)).symm
      (moduleTensorMap
          ((extendRestrictAdj ((augmentation φ).app n)).unit.app
            (relativeDifferentials (standardTerm A (Under.mk φ) n).hom))
          (𝟙 (restrictedDegree φ F n)) ≫
        Restriction.tensorComparison ((augmentation φ).app n)
          ((simplicialModule A (Under.mk φ)).obj n) F)

private def cotangentExtendComponent (n : SimplexCategoryᵒᵖ) :
    ((extensionDegreewise φ).obj (cotangentModule φ F)).obj n ⟶ (simplicialCotangent φ F).obj n :=
  cotangentExtendDegree φ F n

/-- The degreewise scalar comparison commutes with simplicial operators. -/
private theorem cotangentExtend_naturality {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    ((extensionDegreewise φ).obj (cotangentModule φ F)).map f ≫ cotangentExtendComponent φ F m =
      cotangentExtendComponent φ F n ≫ (simplicialCotangent φ F).map f := sorry

/-- Degreewise comparison `extend(Ω_{P_n/A} ⊗ F) ⟶ (extend Ω_{P_n/A}) ⊗ F`. -/
def cotangentExtend :
    (extensionDegreewise φ).obj (cotangentModule φ F) ⟶ simplicialCotangent φ F where
  app := cotangentExtendComponent φ F
  naturality := fun {U V} f => cotangentExtend_naturality φ F f

private def evalAtDegreeFrom_cotangentModuleComponent (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) :
    ((degreeSequence φ F n).X₁).val.obj U ⟶ (evalAtDegree (cotangentModule φ F) n).val.obj U :=
  _root_.ModuleCat.homMk (𝟙 _) (by intro r; ext t; rfl)

/-- The identity on sections commutes with the site restriction maps. -/
private theorem evalAtDegreeFrom_cotangentModule_laws (n : SimplexCategoryᵒᵖ)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    ((degreeSequence φ F n).X₁).val.map f ≫
        (_root_.ModuleCat.restrictScalars _).map (evalAtDegreeFrom_cotangentModuleComponent φ F n V) =
      evalAtDegreeFrom_cotangentModuleComponent φ F n U ≫ (evalAtDegree (cotangentModule φ F) n).val.map f := sorry

/-- The identity on sections identifies degree evaluation with its specified coefficient module. -/
private def evalAtDegreeFrom_cotangentModule (n : SimplexCategoryᵒᵖ) :
    (degreeSequence φ F n).X₁ ⟶ evalAtDegree (cotangentModule φ F) n where
  val :=
    { app := evalAtDegreeFrom_cotangentModuleComponent φ F n
      naturality := fun {U V} f => evalAtDegreeFrom_cotangentModule_laws φ F n f }

/-- The identity-site coefficient morphism of a same-site map of commutative ring sheaves. -/
private def sameSiteCommStructureMap {𝒪 𝒪' : Sheaf J CommRingCat.{u}} (α : 𝒪 ⟶ 𝒪') :
    𝒪 ⟶ ((𝟭 C).sheafPushforwardContinuous CommRingCat.{u} J J).obj 𝒪' :=
  α ≫ (Functor.sheafPushforwardContinuousId CommRingCat.{u} J).inv.app 𝒪'

/-- Inverse tensor comparison of same-site extension of scalars:
`(extend M) ⊗ (extend N) ⟶ extend (M ⊗ N)`. -/
private def extendTensorInv {𝒪 𝒪' : Sheaf J CommRingCat.{u}} (α : 𝒪 ⟶ 𝒪')
    (M N : ringedSiteModuleCategory.{u, u, u, u} J 𝒪) :
    moduleTensor ((extendAlong α).obj M) ((extendAlong α).obj N) ⟶
      (extendAlong α).obj (moduleTensor M N) :=
  moduleTensorMap ((pullbackExtendIso α).inv.app M) ((pullbackExtendIso α).inv.app N) ≫
    (SheafOfModules.Pullback.tensorIso (𝟭 C) (sameSiteCommStructureMap α) M N).inv ≫
    (pullbackExtendIso α).hom.app (moduleTensor M N)

/-- Reverse degreewise associativity
`(Ω_{P_n/A} ⊗_{P_n} B) ⊗_B F ⟶ B ⊗_{P_n} (Ω_{P_n/A} ⊗_{P_n} F)`. -/
def cotangentExtendInvDegree (n : SimplexCategoryᵒᵖ) :
    (simplicialCotangent φ F).obj n ⟶
      ((extensionDegreewise φ).obj (cotangentModule φ F)).obj n :=
  moduleTensorMap (𝟙 ((simplicialModule A (Under.mk φ)).obj n))
      (extendRestrictUnit φ n F) ≫
    extendTensorInv ((augmentation φ).app n)
      (relativeDifferentials (standardTerm A (Under.mk φ) n).hom)
      (restrictedDegree φ F n) ≫
    (extendAlong ((augmentation φ).app n)).map (evalAtDegreeFrom_cotangentModule φ F n)

private def cotangentExtendInvComponent (n : SimplexCategoryᵒᵖ) :
    (simplicialCotangent φ F).obj n ⟶ ((extensionDegreewise φ).obj (cotangentModule φ F)).obj n :=
  cotangentExtendInvDegree φ F n

/-- The degreewise scalar comparison commutes with simplicial operators. -/
private theorem cotangentExtendInv_naturality {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (simplicialCotangent φ F).map f ≫ cotangentExtendInvComponent φ F m =
      cotangentExtendInvComponent φ F n ≫ ((extensionDegreewise φ).obj (cotangentModule φ F)).map f := sorry

/-- Reverse comparison of `cotangentExtend`. -/
def cotangentExtendInv :
    simplicialCotangent φ F ⟶ (extensionDegreewise φ).obj (cotangentModule φ F) where
  app := cotangentExtendInvComponent φ F
  naturality := fun {U V} f => cotangentExtendInv_naturality φ F f

/-- The scalar counit and the unit along a standard augmentation are mutually inverse. -/
private theorem restrictedExtendCounit_laws :
    restrictedExtendCounit φ F ≫ restrictedExtendUnit φ F = 𝟙 _ ∧
      restrictedExtendUnit φ F ≫ restrictedExtendCounit φ F = 𝟙 _ := sorry

/-- The two scalar-extension tensor comparisons are mutually inverse. -/
private theorem cotangentExtend_laws :
    cotangentExtend φ F ≫ cotangentExtendInv φ F = 𝟙 _ ∧
      cotangentExtendInv φ F ≫ cotangentExtend φ F = 𝟙 _ := sorry

/-- The scalar counit for a standard augmentation is invertible with the explicit unit inverse. -/
instance restrictedExtendCounit_isIso : IsIso (restrictedExtendCounit φ F) :=
  ({ hom := restrictedExtendCounit φ F
     inv := restrictedExtendUnit φ F
     hom_inv_id := (restrictedExtendCounit_laws φ F).1
     inv_hom_id := (restrictedExtendCounit_laws φ F).2 } : _ ≅ _).isIso_hom

/-- The degreewise cotangent scalar comparison is invertible with the tensor comparison inverse. -/
instance cotangentExtend_isIso : IsIso (cotangentExtend φ F) :=
  ({ hom := cotangentExtend φ F
     inv := cotangentExtendInv φ F
     hom_inv_id := (cotangentExtend_laws φ F).1
     inv_hom_id := (cotangentExtend_laws φ F).2 } : _ ≅ _).isIso_hom

/-- The Moore complex of the constant simplicial module `F`. -/
private def constantComplex : CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J B) ℤ :=
  (mooreExtend (B := B)).obj (simplicialConstant F)

/-- The cohomological degree `-n` term of `constantComplex` is `F`. -/
private def constantComplex_X (n : ℕ) :
    (constantComplex F).X (-n) ≅ F :=
  extendXIso
    ((alternatingFaceMapComplex (ringedSiteModuleCategory.{u, u, u, u} J B)).obj (simplicialConstant F))
    ComplexShape.embeddingDownNat (rfl : ComplexShape.embeddingDownNat.f n = -n)

/-- The degree-zero component of `constantToSingle` is the identification with `F`. -/
private def constantComplex_X₀ : (constantComplex F).X 0 ≅ F :=
  constantComplex_X F 0

/-- Differentials into degree `0` of `constantComplex` vanish after the identification with
`F`. -/
private theorem constantToSingle_comp (i : ℤ) (hi : (ComplexShape.up ℤ).Rel i 0) :
    (constantComplex F).d i 0 ≫ (constantComplex_X₀ F).hom = 0 :=
  sorry

/-- The quasi-isomorphism from the evaluation complex of `underline{F}` to the degree-zero
single of `F`. -/
def constantToSingle :
    constantComplex F ⟶
      (HomologicalComplex.single (ringedSiteModuleCategory.{u, u, u, u} J B) (ComplexShape.up ℤ) 0).obj F :=
  HomologicalComplex.mkHomToSingle (constantComplex_X₀ F).hom (constantToSingle_comp F)

/-- Differentials out of degree `0` of `constantComplex` vanish before the identification with
`F`. -/
private theorem singleToConstant_comp (k : ℤ) (hk : (ComplexShape.up ℤ).Rel 0 k) :
    (constantComplex_X₀ F).inv ≫ (constantComplex F).d 0 k = 0 :=
  sorry

/-- The reverse comparison from the degree-zero single of `F` to the Moore complex of
`underline{F}`. -/
def singleToConstant :
    (HomologicalComplex.single (ringedSiteModuleCategory.{u, u, u, u} J B) (ComplexShape.up ℤ) 0).obj F ⟶
      constantComplex F :=
  HomologicalComplex.mkHomFromSingle (constantComplex_X₀ F).inv (singleToConstant_comp F)

private def constantIsoSingleHom : DerivedCategory.Q.obj (constantComplex F) ⟶ (DerivedCategory.singleFunctor (ringedSiteModuleCategory.{u, u, u, u} J B) 0).obj F :=
  DerivedCategory.Q.map (constantToSingle F)

private def constantIsoSingleInv : (DerivedCategory.singleFunctor (ringedSiteModuleCategory.{u, u, u, u} J B) 0).obj F ⟶ DerivedCategory.Q.obj (constantComplex F) :=
  DerivedCategory.Q.map (singleToConstant F)

/-- The forward and reverse vertex comparisons are mutually inverse. -/
private theorem constantIsoSingle_laws :
    constantIsoSingleHom F ≫ constantIsoSingleInv F = 𝟙 _ ∧
      constantIsoSingleInv F ≫ constantIsoSingleHom F = 𝟙 _ := sorry

/-- The evaluation complex of the constant simplicial module is identified with the degree-zero
single complex of `F`. -/
def constantIsoSingle :
    DerivedCategory.Q.obj (constantComplex F) ≅
      (DerivedCategory.singleFunctor (ringedSiteModuleCategory.{u, u, u, u} J B) 0).obj F where
  hom := constantIsoSingleHom F
  inv := constantIsoSingleInv F
  hom_inv_id := (constantIsoSingle_laws F).1
  inv_hom_id := (constantIsoSingle_laws F).2

/-- The displayed first vertex `L(φ) ⊗^L F` in `D(B)`. -/
def tensorModule :
    RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J B) :=
  DerivedCategory.DerivedTensor.Bifunctor.obj (C := ringedSiteModuleCategory.{u, u, u, u} J B)
    (DerivedCategory.Q.obj (by exact L(φ)))
    ((DerivedCategory.singleFunctor (ringedSiteModuleCategory.{u, u, u, u} J B) 0).obj F)

/-- The displayed middle vertex `Lπ_!(P¹_{P_•/A}(F))` in `D(B)`. -/
def derivedPrincipalParts :
    RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J B) :=
  (atiyahLowerShriek φ).obj
    ((DerivedCategory.singleFunctor
        (SimplicialSite.ModuleCat.{u, u, u, u} (standardSimplicial φ)) 0).obj
      (principalPartsModule φ F))

/-- The cohomological degree `-n` term of `tensorModuleCochain` is the `n`-th simplicial cotangent
term. -/
private def tensorCochain_X (n : ℕ) :
    (tensorModuleCochain φ F).X (-n) ≅ (simplicialCotangent φ F).obj (op (SimplexCategory.mk n)) :=
  extendXIso
    ((alternatingFaceMapComplex (ringedSiteModuleCategory.{u, u, u, u} J B)).obj
      (simplicialCotangent φ F))
    ComplexShape.embeddingDownNat (rfl : ComplexShape.embeddingDownNat.f n = -n)

/-- `tensorModuleCochain` vanishes in strictly positive cohomological degrees. -/
private theorem isZero_tensorCochain_X_of_pos {n : ℤ} (hn : 0 < n) :
    IsZero ((tensorModuleCochain φ F).X n) :=
  sorry

/-- The ordinary tensor of `L(φ)` with the degree-zero single of `F` vanishes in strictly
positive cohomological degrees. -/
private theorem isZero_cotangentTensorSingle_X_of_pos {n : ℤ} (hn : 0 < n) :
    IsZero
      ((HomologicalComplex.tensorObj (L(φ))
        ((HomologicalComplex.single (ringedSiteModuleCategory.{u, u, u, u} J B)
          (ComplexShape.up ℤ) 0).obj F)).X n) :=
  sorry

/-- The total-complex shape sends `(-n.natAbs, 0)` to `n` when `n = -n.natAbs`. -/
private theorem π_up_neg_natAbs (n : ℤ) (hn : n = -n.natAbs) :
    ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (-(n.natAbs : ℤ), 0) = n :=
  sorry

/-- The summand inclusion of `L(φ).X (-n.natAbs) ⊗ F` into the tensor with the degree-zero
single of `F`. -/
private def ιTensorCotangentSingle (n : ℤ) (hn : n = -n.natAbs) :
    (moduleTensor ((L(φ)).X (-(n.natAbs : ℤ)))
      (((HomologicalComplex.single (ringedSiteModuleCategory.{u, u, u, u} J B)
          (ComplexShape.up ℤ) 0).obj F).X 0)) ⟶
      (HomologicalComplex.tensorObj (L(φ))
        ((HomologicalComplex.single (ringedSiteModuleCategory.{u, u, u, u} J B)
          (ComplexShape.up ℤ) 0).obj F)).X n :=
  HomologicalComplex.ιTensorObj (L(φ))
    ((HomologicalComplex.single (ringedSiteModuleCategory.{u, u, u, u} J B) (ComplexShape.up ℤ) 0).obj F)
    (-(n.natAbs : ℤ)) 0 n (π_up_neg_natAbs n hn)

/-- A non-positive integer equals the negation of its `natAbs`. -/
private theorem eq_neg_natAbs_of_not_pos {n : ℤ} (hn : ¬ 0 < n) : n = -n.natAbs :=
  sorry

/-- The `(i₁, i₂)`-summand of `L(φ) ⊗ single F` in degree `n` identifies with the
`( -n.natAbs, 0 )` summand when those indices match. -/
private theorem tensorCotangentSingle_component_eq (n : ℤ) (hn : n = -n.natAbs)
    (i₁ i₂ : ℤ) (h : i₁ = -(n.natAbs : ℤ) ∧ i₂ = 0)
    (hi : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (i₁, i₂) = n) :
    moduleTensor ((L(φ)).X i₁)
        (((HomologicalComplex.single (ringedSiteModuleCategory.{u, u, u, u} J B)
          (ComplexShape.up ℤ) 0).obj F).X i₂) =
      moduleTensor ((L(φ)).X (-(n.natAbs : ℤ)))
        (((HomologicalComplex.single (ringedSiteModuleCategory.{u, u, u, u} J B)
          (ComplexShape.up ℤ) 0).obj F).X 0) :=
  sorry

/-- The inverse of the summand inclusion `ιTensorCotangentSingle`, as the matching
total-complex projection. -/
private def πTensorCotangentSingle (n : ℤ) (hn : n = -n.natAbs) :
    (HomologicalComplex.tensorObj (L(φ))
      ((HomologicalComplex.single (ringedSiteModuleCategory.{u, u, u, u} J B)
        (ComplexShape.up ℤ) 0).obj F)).X n ⟶
      moduleTensor ((L(φ)).X (-(n.natAbs : ℤ)))
        (((HomologicalComplex.single (ringedSiteModuleCategory.{u, u, u, u} J B)
          (ComplexShape.up ℤ) 0).obj F).X 0) :=
  HomologicalComplex.mapBifunctorDesc
    (fun i₁ i₂ hi =>
      dite (i₁ = -(n.natAbs : ℤ) ∧ i₂ = 0)
        (fun h =>
          eqToHom (tensorCotangentSingle_component_eq φ F n hn i₁ i₂ h hi))
        (fun _ => 0))

/-- The matching tensor summand inclusion and projection are mutually inverse. -/
private theorem tensorCochainXIsoTensorSingle_laws (n : ℤ) (hn : n = -n.natAbs) :
    ιTensorCotangentSingle φ F n hn ≫ πTensorCotangentSingle φ F n hn = 𝟙 _ ∧
      πTensorCotangentSingle φ F n hn ≫ ιTensorCotangentSingle φ F n hn = 𝟙 _ := sorry

/-- The matching tensor summand inclusion is invertible with the explicit total projection. -/
instance ιTensorCotangentSingle_isIso (n : ℤ) (hn : n = -n.natAbs) :
    IsIso (ιTensorCotangentSingle φ F n hn) :=
  ({ hom := ιTensorCotangentSingle φ F n hn
     inv := πTensorCotangentSingle φ F n hn
     hom_inv_id := (tensorCochainXIsoTensorSingle_laws φ F n hn).1
     inv_hom_id := (tensorCochainXIsoTensorSingle_laws φ F n hn).2 } : _ ≅ _).isIso_hom

/-- Degreewise identification of `tensorModuleCochain` with `L(φ) ⊗ single F`. -/
private def tensorCochainXIsoTensorSingle (n : ℤ) :
    (tensorModuleCochain φ F).X n ≅
      (HomologicalComplex.tensorObj (L(φ))
        ((HomologicalComplex.single (ringedSiteModuleCategory.{u, u, u, u} J B)
          (ComplexShape.up ℤ) 0).obj F)).X n :=
  dite (0 < n)
    (fun hn =>
      { hom := 0
        inv := 0
        hom_inv_id := (isZero_tensorCochain_X_of_pos φ F hn).eq_of_src _ _
        inv_hom_id := (isZero_cotangentTensorSingle_X_of_pos φ F hn).eq_of_src _ _ })
    (fun hn =>
      let hn' := eq_neg_natAbs_of_not_pos hn
      HomologicalComplex.XIsoOfEq (tensorModuleCochain φ F) hn' ≪≫
        tensorCochain_X φ F n.natAbs ≪≫
        (tensorRight F).mapIso
          (objXIso A (Under.mk φ) n.natAbs).symm ≪≫
        (whiskerLeftIso ((L(φ)).X (-(n.natAbs : ℤ)))
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).symm) ≪≫
        { hom := ιTensorCotangentSingle φ F n hn'
          inv := πTensorCotangentSingle φ F n hn'
          hom_inv_id := (tensorCochainXIsoTensorSingle_laws φ F n hn').1
          inv_hom_id := (tensorCochainXIsoTensorSingle_laws φ F n hn').2 })

/-- In positive degrees, `tensorCochainXIsoTensorSingle` is the unique map of zero objects. -/
private theorem tensorCochainXIsoTensorSingle_of_pos {n : ℤ} (hn : 0 < n) :
    tensorCochainXIsoTensorSingle φ F n =
      IsZero.iso (isZero_tensorCochain_X_of_pos φ F hn)
        (isZero_cotangentTensorSingle_X_of_pos φ F hn) :=
  by
    apply Iso.ext
    exact (isZero_tensorCochain_X_of_pos φ F hn).eq_of_src _ _

/-- The degreewise cotangent-tensor identifications commute with differentials. -/
private theorem tensorCochainIsoTensorSingle_comm (n m : ℤ) :
    (tensorModuleCochain φ F).d n m ≫ (tensorCochainXIsoTensorSingle φ F m).hom =
      (tensorCochainXIsoTensorSingle φ F n).hom ≫
        (HomologicalComplex.tensorObj (L(φ))
          ((HomologicalComplex.single (ringedSiteModuleCategory.{u, u, u, u} J B)
            (ComplexShape.up ℤ) 0).obj F)).d n m := sorry

/-- Cochain-level identification `tensorModuleCochain ≅ L(φ) ⊗ single F`. -/
def tensorCochainIsoTensorSingle :
    tensorModuleCochain φ F ≅
      HomologicalComplex.tensorObj (L(φ))
        ((HomologicalComplex.single (ringedSiteModuleCategory.{u, u, u, u} J B)
          (ComplexShape.up ℤ) 0).obj F) :=
  HomologicalComplex.Hom.isoOfComponents (tensorCochainXIsoTensorSingle φ F)
    (fun n m _ => (tensorCochainIsoTensorSingle_comm φ F n m).symm)

/-- The degree-`n` component of `tensorCochainIsoTensorSingle` is
`tensorCochainXIsoTensorSingle`. -/
theorem tensorCochainIsoTensorSingle_hom_f (n : ℤ) :
    (tensorCochainIsoTensorSingle φ F).hom.f n =
      (tensorCochainXIsoTensorSingle φ F n).hom :=
  rfl

/-- The two-variable derived-tensor counit at the cochain models of `L(φ)` and `F`. -/
def tensorCounitApp :
    DerivedCategory.DerivedTensor.Bifunctor.obj (C := ringedSiteModuleCategory.{u, u, u, u} J B)
        (DerivedCategory.Q.obj (by exact L(φ)))
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (ringedSiteModuleCategory.{u, u, u, u} J B)
            (ComplexShape.up ℤ) 0).obj F)) ⟶
      DerivedCategory.Q.obj
        (HomologicalComplex.tensorObj (L(φ))
          ((HomologicalComplex.single (ringedSiteModuleCategory.{u, u, u, u} J B)
            (ComplexShape.up ℤ) 0).obj F)) :=
  DerivedCategory.DerivedTensor.Bifunctor.counitAppOfQ (C := ringedSiteModuleCategory.{u, u, u, u} J B)
    (by exact L(φ))
    ((HomologicalComplex.single (ringedSiteModuleCategory.{u, u, u, u} J B)
      (ComplexShape.up ℤ) 0).obj F)

/-- The two-variable derived-tensor counit at the cochain models of `L(φ)` and `F` is a
quasi-isomorphism on its actual homotopy representative. -/
theorem tensorCounitApp_quasiIso :
    HomotopyCategory.quasiIso (ringedSiteModuleCategory.{u, u, u, u} J B) (ComplexShape.up ℤ)
      (Localization.arrowRepresentative DerivedCategory.Qh (tensorCounitApp φ F)).hom :=
  sorry

/-- Identification of the two-variable derived tensor of the cochain models with ordinary
tensor, by inverting the counit through the localization formal inverse. -/
def tensorCounitAppIso :
    DerivedCategory.DerivedTensor.Bifunctor.obj (C := ringedSiteModuleCategory.{u, u, u, u} J B)
        (DerivedCategory.Q.obj (by exact L(φ)))
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (ringedSiteModuleCategory.{u, u, u, u} J B)
            (ComplexShape.up ℤ) 0).obj F)) ≅
      DerivedCategory.Q.obj
        (HomologicalComplex.tensorObj (L(φ))
          ((HomologicalComplex.single (ringedSiteModuleCategory.{u, u, u, u} J B)
            (ComplexShape.up ℤ) 0).obj F)) :=
  Localization.formalIsoOfArrowRepresentative
    (HomotopyCategory.quasiIso (ringedSiteModuleCategory.{u, u, u, u} J B) (ComplexShape.up ℤ))
    DerivedCategory.Qh (tensorCounitApp φ F) (tensorCounitApp_quasiIso φ F)

/-- Transport of the second derived-tensor factor from `Q (single F)` to `single F`. -/
def tensorModuleIsoBifunctorQ :
    DerivedCategory.DerivedTensor.Bifunctor.obj (C := ringedSiteModuleCategory.{u, u, u, u} J B)
        (DerivedCategory.Q.obj (by exact L(φ)))
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (ringedSiteModuleCategory.{u, u, u, u} J B)
            (ComplexShape.up ℤ) 0).obj F)) ≅
      tensorModule φ F :=
  (DerivedCategory.DerivedTensor.Bifunctor.leftFunctor (C := ringedSiteModuleCategory.{u, u, u, u} J B)
      ((DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J B) ℤ ⥤
        DerivedCategory (ringedSiteModuleCategory.{u, u, u, u} J B)).obj L(φ))).mapIso
    ((DerivedCategory.singleFunctorIsoCompQ (ringedSiteModuleCategory.{u, u, u, u} J B) 0).app F).symm

/-- Comparison `Lπ_!(single X) ⟶ evaluation (single (extend X))` from the homotopy-to-derived
counit after Moore evaluation. -/
def atiyahLowerShriekToMoore
    (X : SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ)) :
    (atiyahLowerShriek φ).obj
        ((DerivedCategory.singleFunctor
            (SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ)) 0).obj X) ⟶
      (evaluation (B := B)).obj
        ((DerivedCategory.singleFunctor
            (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B) 0).obj
          ((extensionDegreewise φ).obj X)) :=
  (evaluation (B := B)).map (derivedExtensionSingle φ X)

/-- The degree-zero single of the assembled simplicial principal-parts sequence. -/
private def atiyahSequence_singleComplex :
    ShortComplex
      (CochainComplex (SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ)) ℤ) :=
  (HomologicalComplex.single
      (SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ))
      (ComplexShape.up ℤ) 0).mapShortComplex.obj (atiyahSequence φ F)

/-- The mapping-cone description of the third vertex of the degree-zero single sequence. -/
def atiyahSequence_desc :
    CochainComplex.mappingCone (atiyahSequence_singleComplex φ F).f ⟶
      (atiyahSequence_singleComplex φ F).X₃ :=
  CochainComplex.mappingCone.descShortComplex (atiyahSequence_singleComplex φ F)

/-- `atiyahSequence_desc` is a quasi-isomorphism. -/
theorem atiyahSequence_desc_quasiIso :
    HomologicalComplex.quasiIso
      (SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ))
      (ComplexShape.up ℤ) (atiyahSequence_desc φ F) :=
  sorry

/-- Localization inverse of the concrete mapping-cone description. -/
def atiyahSequence_descIso :=
  CategoryTheory.Localization.formalIso
    (HomologicalComplex.quasiIso
      (SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ)) (ComplexShape.up ℤ))
    (DerivedCategory.Q :
      CochainComplex (SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ)) ℤ ⥤
        DerivedCategory (SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ)))
    (atiyahSequence_desc φ F) (atiyahSequence_desc_quasiIso φ F)

/-- The SES connecting map in `D(P_•)`, obtained from the mapping cone of `atiyahSequence_f`
by inverting the concrete quasi-isomorphism `atiyahSequence_desc`. -/
def atiyahSequence_connecting :
    (DerivedCategory.singleFunctor
        (SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ)) 0).obj
      (restrictedModule φ F) ⟶
      ((DerivedCategory.singleFunctor
          (SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ)) 0).obj
        (cotangentModule φ F))⟦(1 : ℤ)⟧ :=
  (DerivedCategory.singleFunctorIsoCompQ
      (SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ)) 0).hom.app
    (restrictedModule φ F) ≫
  (atiyahSequence_descIso φ F).inv ≫
  DerivedCategory.Q.map
    (CochainComplex.mappingCone.triangle
      ((HomologicalComplex.single
          (SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ))
          (ComplexShape.up ℤ) 0).map (atiyahSequence_f φ F))).mor₃ ≫
  (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
    ((HomologicalComplex.single
        (SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ))
        (ComplexShape.up ℤ) 0).obj (cotangentModule φ F)) ≫
  ((DerivedCategory.singleFunctorIsoCompQ
      (SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ)) 0).inv.app
    (cotangentModule φ F))⟦(1 : ℤ)⟧'

/-- The principal-parts sequence triangle after derived augmentation lower shriek, with
its mapping-cone boundary. -/
def atiyahTriangle_ofSES :
    Triangle (RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J B)) :=
  (atiyahLowerShriek φ).mapTriangle.obj
    (Triangle.mk
      ((DerivedCategory.singleFunctor
        (SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ)) 0).map
          (atiyahSequence_f φ F))
      ((DerivedCategory.singleFunctor
        (SimplicialSite.ModuleCat.{u, u, u, u} (J := J) (standardSimplicial φ)) 0).map
          (atiyahSequence_g φ F))
      (atiyahSequence_connecting φ F))

/-- Derived augmentation lower shriek takes the principal-parts sequence to a distinguished triangle. -/
theorem atiyahTriangle_ofSES_distinguished :
    atiyahTriangle_ofSES φ F ∈
      distTriang (RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J B)) := sorry

private def tensorIsoHom : (atiyahTriangle_ofSES φ F).obj₁ ⟶ tensorModule φ F :=
  atiyahLowerShriekToMoore φ (cotangentModule φ F) ≫
        (evaluation (B := B)).map
          ((DerivedCategory.singleFunctor
              (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B) 0).map
            (cotangentExtend φ F)) ≫
          (evaluationSingleIso (B := B) (simplicialCotangent φ F)).hom ≫
            DerivedCategory.Q.map (tensorCochainIsoTensorSingle φ F).hom ≫
              (tensorCounitAppIso φ F).inv ≫
                (tensorModuleIsoBifunctorQ φ F).hom

private def tensorIsoInv : tensorModule φ F ⟶ (atiyahTriangle_ofSES φ F).obj₁ :=
  (tensorModuleIsoBifunctorQ φ F).inv ≫
      (tensorCounitAppIso φ F).hom ≫
        DerivedCategory.Q.map (tensorCochainIsoTensorSingle φ F).inv ≫
          (evaluationSingleIso (B := B) (simplicialCotangent φ F)).inv ≫
            (evaluation (B := B)).map
              ((DerivedCategory.singleFunctor
                  (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B) 0).map
                (cotangentExtendInv φ F)) ≫
              cotangentComparisonInv φ F

/-- The forward and reverse vertex comparisons are mutually inverse. -/
private theorem tensorIso_laws :
    tensorIsoHom φ F ≫ tensorIsoInv φ F = 𝟙 _ ∧
      tensorIsoInv φ F ≫ tensorIsoHom φ F = 𝟙 _ := sorry

/-- The comparison isomorphism `Lπ_!(Ω_{P_•/A} ⊗ F) ≅ L(φ) ⊗^L F`. -/
def tensorIso :
    (atiyahTriangle_ofSES φ F).obj₁ ≅ tensorModule φ F where
  hom := tensorIsoHom φ F
  inv := tensorIsoInv φ F
  hom_inv_id := (tensorIso_laws φ F).1
  inv_hom_id := (tensorIso_laws φ F).2

private def moduleIsoHom : (atiyahTriangle_ofSES φ F).obj₃ ⟶ (DerivedCategory.singleFunctor (ringedSiteModuleCategory.{u, u, u, u} J B) 0).obj F :=
  atiyahLowerShriekToMoore φ (restrictedModule φ F) ≫
        (evaluation (B := B)).map
          ((DerivedCategory.singleFunctor
              (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B) 0).map
            (restrictedExtendCounit φ F)) ≫
          (evaluationSingleIso (B := B) (simplicialConstant F)).hom ≫
            (constantIsoSingle F).hom

private def moduleIsoInv : (DerivedCategory.singleFunctor (ringedSiteModuleCategory.{u, u, u, u} J B) 0).obj F ⟶ (atiyahTriangle_ofSES φ F).obj₃ :=
  (constantIsoSingle F).inv ≫
      (evaluationSingleIso (B := B) (simplicialConstant F)).inv ≫
        (evaluation (B := B)).map
          ((DerivedCategory.singleFunctor
              (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory.{u, u, u, u} J B) 0).map
            (restrictedExtendUnit φ F)) ≫
          restrictedComparisonInv φ F

/-- The forward and reverse vertex comparisons are mutually inverse. -/
private theorem moduleIso_laws :
    moduleIsoHom φ F ≫ moduleIsoInv φ F = 𝟙 _ ∧
      moduleIsoInv φ F ≫ moduleIsoHom φ F = 𝟙 _ := sorry

/-- The comparison isomorphism `Lπ_!(restricted F) ≅ F`. -/
def moduleIso :
    (atiyahTriangle_ofSES φ F).obj₃ ≅
      (DerivedCategory.singleFunctor (ringedSiteModuleCategory.{u, u, u, u} J B) 0).obj F where
  hom := moduleIsoHom φ F
  inv := moduleIsoInv φ F
  hom_inv_id := (moduleIso_laws φ F).1
  inv_hom_id := (moduleIso_laws φ F).2

/-- The first map `L(φ) ⊗^L F ⟶ Lπ_!(P¹_{P_•/A}(F))` of the displayed triangle. -/
def tensorToPrincipalParts :
    tensorModule φ F ⟶ derivedPrincipalParts φ F :=
  (tensorIso φ F).inv ≫ (atiyahTriangle_ofSES φ F).mor₁

/-- The second map `Lπ_!(P¹_{P_•/A}(F)) ⟶ F` of the displayed triangle. -/
def principalPartsToModule :
    derivedPrincipalParts φ F ⟶
      (DerivedCategory.singleFunctor (ringedSiteModuleCategory.{u, u, u, u} J B) 0).obj F :=
  (atiyahTriangle_ofSES φ F).mor₂ ≫ (moduleIso φ F).hom

/-- The Atiyah class `F ⟶ (L(φ) ⊗^L F)⟦1⟧`, the connecting map of the displayed triangle. -/
def atiyahClass :
    (DerivedCategory.singleFunctor (ringedSiteModuleCategory.{u, u, u, u} J B) 0).obj F ⟶
      (tensorModule φ F)⟦(1 : ℤ)⟧ :=
  (moduleIso φ F).inv ≫
    (atiyahTriangle_ofSES φ F).mor₃ ≫
      (shiftFunctor (RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J B))
          (1 : ℤ)).map (tensorIso φ F).hom

/-- The displayed distinguished triangle
`L(φ) ⊗^L F ⟶ Lπ_!(P¹_{P_•/A}(F)) ⟶ F ⟶ (L(φ) ⊗^L F)⟦1⟧` in `D(B)`. -/
def atiyahTriangle :
    Triangle (RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J B)) :=
  Triangle.mk (tensorToPrincipalParts φ F) (principalPartsToModule φ F)
    (atiyahClass φ F)

/-- The first vertex of `atiyahTriangle` is `tensorModule`. -/
theorem atiyahTriangle_obj₁ :
    (atiyahTriangle φ F).obj₁ = tensorModule φ F :=
  rfl

/-- The second vertex of `atiyahTriangle` is `derivedPrincipalParts`. -/
theorem atiyahTriangle_obj₂ :
    (atiyahTriangle φ F).obj₂ = derivedPrincipalParts φ F :=
  rfl

/-- The third vertex of `atiyahTriangle` is the image of `F` under the degree-zero single
functor. -/
theorem atiyahTriangle_obj₃ :
    (atiyahTriangle φ F).obj₃ =
      (DerivedCategory.singleFunctor (ringedSiteModuleCategory.{u, u, u, u} J B) 0).obj F :=
  rfl

/-- The first morphism of `atiyahTriangle` is `tensorToPrincipalParts`. -/
theorem atiyahTriangle_mor₁ :
    (atiyahTriangle φ F).mor₁ = tensorToPrincipalParts φ F :=
  rfl

/-- The second morphism of `atiyahTriangle` is `principalPartsToModule`. -/
theorem atiyahTriangle_mor₂ :
    (atiyahTriangle φ F).mor₂ = principalPartsToModule φ F :=
  rfl

/-- The third morphism of `atiyahTriangle` is `atiyahClass`. -/
theorem atiyahTriangle_mor₃ :
    (atiyahTriangle φ F).mor₃ = atiyahClass φ F :=
  rfl

/-- The Atiyah triangle of `F` along `φ` is distinguished in `D(B)`. -/
theorem atiyahTriangle_distinguished :
    atiyahTriangle φ F ∈
      distTriang (RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J B)) :=
  sorry

end SheafOfModules.RingedSite.CotangentComplex
