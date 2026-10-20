/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.IrreducibleComponent.Multiplicity
public import stacks_project.Chap101.Definition_101_8_1_Noetherian
public import stacks_project.Chap101.Definition_101_13_2_Closed

/-!
# Multiplicities of irreducible components of algebraic stacks

The multiplicity of an irreducible component of a locally Noetherian algebraic
stack is the scheme-level multiplicity of any dominating smooth locally
Noetherian scheme chart. Independence of the chart is recorded separately; the
numerical value is observable `ℕ`-valued data.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped Bicategory

noncomputable section

universe u

#check (AlgebraicGeometry.AlgebraicStack.irreducibleComponentMultiplicity :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [AlgebraicGeometry.AlgebraicStack.IsLocallyNoetherian X]
    (τ : TopologicalSpace (AlgebraicGeometry.AlgebraicStack.Points X)),
    @irreducibleComponents (AlgebraicGeometry.AlgebraicStack.Points X) τ → ℕ)
