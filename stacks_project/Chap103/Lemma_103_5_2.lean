/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Fppf.ModuleRule
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 103.5.2: fppf higher direct images along quasi-compact quasi-separated
morphisms preserve weak Serre rules satisfying smooth descent and affine
higher-direct-image stability. -/
@[stacks 0770] #check (AlgebraicGeometry.AlgebraicStack.FppfModuleRule.mapsHigherDirectImage :
  ∀ {S : Scheme.{u}} (M : FppfModuleRule S)
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (i : ℕ),
    M.predicate X ≤ (M.predicate Y).inverseImage (fppfHigherDirectImageFunctor f i))

#check (AlgebraicGeometry.AlgebraicStack.FppfModuleRule.mem_higherDirectImage :
  ∀ {S : Scheme.{u}} (M : FppfModuleRule S)
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (i : ℕ)
    {F : fppfModules X}, M.predicate X F →
    M.predicate Y ((fppfHigherDirectImageFunctor f i).obj F))
