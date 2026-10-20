/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Lemma_67_15_2
public import stacks_project.Chap75.Lemma_75_7_4_Preimage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support.Proper

/-!
# Closed support of modules on algebraic spaces

The closed support of an `𝒪_X`-module is the topological closure of its
étale-site support. For a finite-type quasi-coherent module this coincides
with the support itself, and properness of closed support over a base is
preserved by pullback in a cartesian square.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

noncomputable section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.closedSupport :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S},
    X.Modules → Closeds (AlgebraicSpace.Points X))
