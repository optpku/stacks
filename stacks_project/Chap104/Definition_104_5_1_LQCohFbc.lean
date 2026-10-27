/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import ReasLib.CategoryTheory.Sites.MorphismOfSites.Topology
public import stacks_project.Chap96.Definition_96_11_1_QCoh
public import stacks_project.Chap96.Lemma_96_12_4_LQCoh
public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import stacks_project.Chap103.Definition_103_7_1_FlatBaseChange
public import stacks_project.Chap103.Definition_103_9_1_Parasitic

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange

/-!
# Module conditions and restriction

Typed compatibility checks for the module conditions, full subcategories, and
restriction functor, with the prerequisite exports retained.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open FiberedCategoryOver.Groupoids Functor.Fiber Opposite Limits
open scoped Bicategory ZeroObject

universe u

namespace AlgebraicGeometry.GroupoidsOver

#check (AlgebraicGeometry.GroupoidsOver.lqcohFbc :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    ObjectProperty (etaleModules X))

#check (AlgebraicGeometry.GroupoidsOver.lqcohFbc_iff :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X),
    lqcohFbc X F ↔ IsLocallyQuasiCoherent F ∧ HasFlatBaseChange F)

#check (AlgebraicGeometry.GroupoidsOver.lqcohFbc_isWeakSerreClass :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    IsWeakSerreClass (lqcohFbc X))

#check (AlgebraicGeometry.GroupoidsOver.LQCohFbc :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    Type (u + 1))

namespace LQCohFbc

#check (AlgebraicGeometry.GroupoidsOver.LQCohFbc.inclusion :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    LQCohFbc X ⥤ etaleModules X)

end LQCohFbc

namespace EtaleModules

#check (AlgebraicGeometry.GroupoidsOver.EtaleModules.IsParasitic :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X),
    Prop)

#check (AlgebraicGeometry.GroupoidsOver.EtaleModules.isParasitic_spec :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X),
    IsParasitic F ↔
      ∀ {U : Over S} (x : X.p.Fiber U),
        AlgebraicStack.Flat (YonedaSlice.representative x) →
          IsZero (F.val.obj (op (fiberInclusion.obj x))))

#check (AlgebraicGeometry.GroupoidsOver.EtaleModules.IsParasitic.isZero :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {F : etaleModules X} [IsParasitic F] {U : Over S} (x : X.p.Fiber U)
    (hx : AlgebraicStack.Flat (YonedaSlice.representative x)),
    IsZero (F.val.obj (op (fiberInclusion.obj x))))

#check (AlgebraicGeometry.GroupoidsOver.EtaleModules.instIsParasitic_of_isZero :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    IsParasitic (0 : etaleModules X))

#check (AlgebraicGeometry.GroupoidsOver.EtaleModules.isParasitic_of_isZero :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {F : etaleModules X} (hF : IsZero F),
    IsParasitic F)

#check (AlgebraicGeometry.GroupoidsOver.EtaleModules.parasitic :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    ObjectProperty (etaleModules X))

#check (AlgebraicGeometry.GroupoidsOver.EtaleModules.mem_parasitic :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X),
    parasitic X F ↔ IsParasitic F)

#check (AlgebraicGeometry.GroupoidsOver.EtaleModules.parasitic_isWeakSerreClass :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    IsWeakSerreClass (parasitic X))

end EtaleModules

#check (AlgebraicGeometry.GroupoidsOver.parasiticLQCohFbc :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    ObjectProperty (etaleModules X))

#check (AlgebraicGeometry.GroupoidsOver.parasiticLQCohFbc_iff :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X),
    parasiticLQCohFbc X F ↔
      EtaleModules.IsParasitic F ∧ IsLocallyQuasiCoherent F ∧
        HasFlatBaseChange F)

#check (AlgebraicGeometry.GroupoidsOver.parasiticLQCohFbc_isWeakSerreClass :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    IsWeakSerreClass (parasiticLQCohFbc X))

#check (AlgebraicGeometry.GroupoidsOver.fppfModules :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    Type (u + 1))

#check (AlgebraicGeometry.GroupoidsOver.fppfModulesIsNormalMonoCategory :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    IsNormalMonoCategory (fppfModules X))

#check (AlgebraicGeometry.GroupoidsOver.fppfModulesIsNormalEpiCategory :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    IsNormalEpiCategory (fppfModules X))

#check (AlgebraicGeometry.GroupoidsOver.fppfModulesHasFiniteProducts :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    HasFiniteProducts (fppfModules X))

#check (AlgebraicGeometry.GroupoidsOver.fppfModulesHasKernels :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    HasKernels (fppfModules X))

#check (AlgebraicGeometry.GroupoidsOver.fppfModulesHasCokernels :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    HasCokernels (fppfModules X))

#check (AlgebraicGeometry.GroupoidsOver.fppfModulesAbelian :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    Abelian (fppfModules X))

#check (AlgebraicGeometry.GroupoidsOver.instEtaleIdIsContinuousFppf :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    (𝟭 X.total).IsContinuous
      (etaleRingedSite X).siteTopology (ringedSite X).siteTopology)

#check (AlgebraicGeometry.GroupoidsOver.instEtaleIdIsMorphismOfSites :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    IsMorphismOfSites
      (etaleRingedSite X).siteTopology (ringedSite X).siteTopology
      (𝟭 X.total))

#check (AlgebraicGeometry.GroupoidsOver.etaleToFppfStructureSheafMap :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    (etaleRingedSite X).structureSheaf ⟶
      ((𝟭 X.total).sheafPushforwardContinuous RingCat.{u}
        (etaleRingedSite X).siteTopology
        (ringedSite X).siteTopology).obj
        (ringedSite X).structureSheaf)

#check (AlgebraicGeometry.GroupoidsOver.etaleFppfHom :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    RingedSite.Hom (ringedSite X) (etaleRingedSite X))

#check (AlgebraicGeometry.GroupoidsOver.etaleFppfHom_base :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    (etaleFppfHom X).base = 𝟭 X.total)

#check (AlgebraicGeometry.GroupoidsOver.restriction :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    fppfModules X ⥤ etaleModules X)

namespace FppfModules

#check (AlgebraicGeometry.GroupoidsOver.FppfModules.lqcohFbc :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    ObjectProperty (fppfModules X))

#check (AlgebraicGeometry.GroupoidsOver.FppfModules.lqcohFbc_iff :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (F : fppfModules X),
    lqcohFbc X F ↔
      IsLocallyQuasiCoherent ((restriction X).obj F) ∧
        HasFlatBaseChange ((restriction X).obj F))

#check (AlgebraicGeometry.GroupoidsOver.FppfModules.lqcohFbc_isWeakSerreClass :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    IsWeakSerreClass (lqcohFbc X))

#check (AlgebraicGeometry.GroupoidsOver.FppfModules.LQCohFbc :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    Type (u + 1))

#check (AlgebraicGeometry.GroupoidsOver.FppfModules.inclusion :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    LQCohFbc X ⥤ fppfModules X)

#check (AlgebraicGeometry.GroupoidsOver.FppfModules.parasitic :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    ObjectProperty (fppfModules X))

#check (AlgebraicGeometry.GroupoidsOver.FppfModules.mem_parasitic :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (F : fppfModules X),
    parasitic X F ↔ IsParasitic F.val)

#check (AlgebraicGeometry.GroupoidsOver.FppfModules.isParasitic_spec :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (F : fppfModules X),
    parasitic X F ↔
      ∀ {U : Over S} (x : X.p.Fiber U),
        AlgebraicStack.Flat (YonedaSlice.representative x) →
          IsZero (F.val.obj (op (fiberInclusion.obj x))))

#check (AlgebraicGeometry.GroupoidsOver.FppfModules.parasitic_zero :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    parasitic X (0 : fppfModules X))

#check (AlgebraicGeometry.GroupoidsOver.FppfModules.parasitic_isWeakSerreClass :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    IsWeakSerreClass (parasitic X))

#check (AlgebraicGeometry.GroupoidsOver.FppfModules.parasiticLQCohFbc :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    ObjectProperty (fppfModules X))

#check (AlgebraicGeometry.GroupoidsOver.FppfModules.parasiticLQCohFbc_iff :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (F : fppfModules X),
    parasiticLQCohFbc X F ↔
      IsParasitic F.val ∧
        IsLocallyQuasiCoherent ((restriction X).obj F) ∧
          HasFlatBaseChange ((restriction X).obj F))

#check (AlgebraicGeometry.GroupoidsOver.FppfModules.parasiticLQCohFbc_isWeakSerreClass :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    IsWeakSerreClass (parasiticLQCohFbc X))

end FppfModules

end AlgebraicGeometry.GroupoidsOver
