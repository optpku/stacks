/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Commutative
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Quasicoherent
public import stacks_project.Chap66.Lemma_66_29_7_CommSheaf

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory SheafOfModules.RingedSite

universe u

variable {S : Scheme.{u}} (X : AlgebraicSpace S)
variable (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X) ℕ)
variable [𝒜.IsCommutative]

/- Situation 71.11.1: here `S` is a scheme, `X` is an algebraic space over `S`,
and `𝒜` is an ℕ-graded commutative quasi-coherent `𝒪_X`-algebra. -/
@[stacks 0849] #check
  (SheafOfModules.RingedSite.GradedAlgebraSheaf.IsQuasicoherent 𝒜 : Prop)
