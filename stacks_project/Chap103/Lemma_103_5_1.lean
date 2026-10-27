/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale.ModuleRule
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale.SmallSections
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.HigherDirectImage.Restriction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 103.5.1: étale higher direct images along quasi-compact quasi-separated
morphisms preserve weak Serre rules satisfying smooth descent and affine
higher-direct-image stability. -/
@[stacks 076Z] #check (AlgebraicGeometry.AlgebraicStack.mapsHigherDirectImage :
  ∀ {S : Scheme.{u}} (M : EtaleModuleRule S)
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (i : ℕ),
    M.predicate X ≤ (M.predicate Y).inverseImage (etaleHigherDirectImageLiftFunctor f i))

#check (AlgebraicGeometry.AlgebraicStack.mem_higherDirectImage :
  ∀ {S : Scheme.{u}} (M : EtaleModuleRule S)
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (i : ℕ)
    {F : EtaleModulesLift X}, M.predicate X F →
    M.predicate Y ((etaleHigherDirectImageLiftFunctor f i).obj F))
