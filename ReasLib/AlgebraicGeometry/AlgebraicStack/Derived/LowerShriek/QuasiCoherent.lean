/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.LowerShriek
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.LowerShriek
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange

/-!
# Quasi-coherence of derived module lower shriek

Derived lower shriek of a quasi-coherent module on the lisse-étale or flat-fppf
site of an algebraic stack has locally quasi-coherent cohomology with flat base
change. For fppf modules these properties are expressed after étale restriction.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.GroupoidsOver CategoryTheory
open ComplexShape RingedSite.Cocontinuous

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- Every cohomology sheaf of derived lower shriek of a quasi-coherent
lisse-étale module is locally quasi-coherent and has flat base change. -/
@[stacks 07B3]
theorem lisseEtaleModuleLowerShriek.homology_mem_lqcohFbc
    {X : GroupoidsOver S} [AlgebraicStack X]
    (H : SheafOfModules.{u} (lisseEtaleStructureSheaf X))
    [H.IsQuasicoherent] (p : ℤ) :
    lqcohFbc X (lisseEtaleModuleLowerShriek.homology X H p) :=
  sorry

/-- Cohomology of derived lower shriek of a quasi-coherent lisse-étale module
is locally quasi-coherent and has the flat base change property. -/
theorem lisseEtaleModuleLowerShriek.homology_spec
    {X : GroupoidsOver S} [AlgebraicStack X]
    (H : SheafOfModules.{u} (lisseEtaleStructureSheaf X))
    [H.IsQuasicoherent] (p : ℤ) :
    IsLocallyQuasiCoherent (lisseEtaleModuleLowerShriek.homology X H p) ∧
      HasFlatBaseChange (lisseEtaleModuleLowerShriek.homology X H p) :=
  (GroupoidsOver.lqcohFbc_iff _).mp (lisseEtaleModuleLowerShriek.homology_mem_lqcohFbc H p)

/-- Degree-`p` cohomology of `Lg_! H` on the lisse-étale comparison is locally
quasi-coherent. -/
instance lisseEtaleModuleLowerShriek.homology.instIsLocallyQuasiCoherent
    {X : GroupoidsOver S} [AlgebraicStack X]
    (H : SheafOfModules.{u} (lisseEtaleStructureSheaf X))
    [H.IsQuasicoherent] (p : ℤ) :
    IsLocallyQuasiCoherent (lisseEtaleModuleLowerShriek.homology X H p) :=
  (lisseEtaleModuleLowerShriek.homology_spec H p).1

/-- Degree-`p` cohomology of `Lg_! H` on the lisse-étale comparison has the
flat base change property. -/
instance lisseEtaleModuleLowerShriek.homology.instHasFlatBaseChange
    {X : GroupoidsOver S} [AlgebraicStack X]
    (H : SheafOfModules.{u} (lisseEtaleStructureSheaf X))
    [H.IsQuasicoherent] (p : ℤ) :
    HasFlatBaseChange (lisseEtaleModuleLowerShriek.homology X H p) :=
  (lisseEtaleModuleLowerShriek.homology_spec H p).2

/-- `Lg_! H` has cohomology in étale `LQCoh^{fbc}` for quasi-coherent lisse-étale
`H`. -/
theorem lisseEtaleModuleLowerShriek.singleDerived_cohomologyIn_lqcohFbc
    {X : GroupoidsOver S} [AlgebraicStack X]
    (H : SheafOfModules.{u} (lisseEtaleStructureSheaf X))
    [H.IsQuasicoherent] :
    DerivedCategory.cohomologyIn (lqcohFbc X)
      (lisseEtaleModuleLowerShriek.singleDerived X H) :=
  fun p ↦ lisseEtaleModuleLowerShriek.homology_mem_lqcohFbc H p

/-- Every cohomology sheaf of derived lower shriek of a quasi-coherent
flat-fppf module has locally quasi-coherent étale restriction with flat base
change. -/
@[stacks 07B3]
theorem flatFppfModuleLowerShriek.homology_mem_lqcohFbc
    {X : GroupoidsOver S} [AlgebraicStack X]
    (H : SheafOfModules.{u} (flatFppfStructureSheaf X))
    [H.IsQuasicoherent] (p : ℤ) :
    FppfModules.lqcohFbc X (flatFppfModuleLowerShriek.homology X H p) :=
  sorry

/-- The étale restriction of cohomology of derived lower shriek of a
quasi-coherent flat-fppf module is locally quasi-coherent and has flat base
change. -/
theorem flatFppfModuleLowerShriek.homology_spec
    {X : GroupoidsOver S} [AlgebraicStack X]
    (H : SheafOfModules.{u} (flatFppfStructureSheaf X))
    [H.IsQuasicoherent] (p : ℤ) :
    IsLocallyQuasiCoherent
        ((restriction X).obj (flatFppfModuleLowerShriek.homology X H p)) ∧
      HasFlatBaseChange
        ((restriction X).obj (flatFppfModuleLowerShriek.homology X H p)) :=
  (FppfModules.lqcohFbc_iff _).mp (flatFppfModuleLowerShriek.homology_mem_lqcohFbc H p)

/-- Degree-`p` cohomology of `Lg_! H` on the flat-fppf comparison is locally
quasi-coherent after étale restriction. -/
instance flatFppfModuleLowerShriek.homology.instIsLocallyQuasiCoherent
    {X : GroupoidsOver S} [AlgebraicStack X]
    (H : SheafOfModules.{u} (flatFppfStructureSheaf X))
    [H.IsQuasicoherent] (p : ℤ) :
    IsLocallyQuasiCoherent
      ((restriction X).obj (flatFppfModuleLowerShriek.homology X H p)) :=
  (flatFppfModuleLowerShriek.homology_spec H p).1

/-- Degree-`p` cohomology of `Lg_! H` on the flat-fppf comparison has the
flat base change property after étale restriction. -/
instance flatFppfModuleLowerShriek.homology.instHasFlatBaseChange
    {X : GroupoidsOver S} [AlgebraicStack X]
    (H : SheafOfModules.{u} (flatFppfStructureSheaf X))
    [H.IsQuasicoherent] (p : ℤ) :
    HasFlatBaseChange
      ((restriction X).obj (flatFppfModuleLowerShriek.homology X H p)) :=
  (flatFppfModuleLowerShriek.homology_spec H p).2

/-- `Lg_! H` has cohomology in fppf `LQCoh^{fbc}` for quasi-coherent flat-fppf
`H`. -/
theorem flatFppfModuleLowerShriek.singleDerived_cohomologyIn_lqcohFbc
    {X : GroupoidsOver S} [AlgebraicStack X]
    (H : SheafOfModules.{u} (flatFppfStructureSheaf X))
    [H.IsQuasicoherent] :
    DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X)
      (flatFppfModuleLowerShriek.singleDerived X H) :=
  fun p ↦ flatFppfModuleLowerShriek.homology_mem_lqcohFbc H p

end AlgebraicGeometry.AlgebraicStack
