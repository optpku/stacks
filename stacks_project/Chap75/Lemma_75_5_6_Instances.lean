/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectTensorComparison
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import stacks_project.Chap66.Lemma_66_29_7_CommSheaf
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh

/-!
# Derived tensor instances for modules on algebraic spaces

Module sheaves on the small étale site of an algebraic space inherit the canonical commutative
ringed-site tensor product, which is the source of unbounded fixed-right derived tensoring.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory ComplexShape
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- Module sheaves on an algebraic space inherit the canonical tensor product of the commutative
small étale ringed site through the specified restriction-of-scalars equivalence. -/
noncomputable abbrev modulesMonoidalCategory : MonoidalCategory X.Modules :=
  Modules.instMonoidalCategory X

/-- The tensor product of `𝒪_X`-modules is additive in each variable. -/
abbrev modulesMonoidalPreadditive : MonoidalPreadditive X.Modules :=
  AlgebraicSpace.modulesMonoidalPreadditive X

/-- Totalized tensor products of unbounded complexes of `𝒪_X`-modules exist. -/
abbrev modulesHasMapBifunctor (K L : CochainComplex X.Modules ℤ) :
    HomologicalComplex.HasMapBifunctor K L (curriedTensor X.Modules) (up ℤ) :=
  AlgebraicSpace.modulesHasMapBifunctor X K L

#check (hasDerivedTensorRight :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), DerivedTensor.Right.Has (C := X.Modules))

end AlgebraicGeometry.AlgebraicSpace.Modules
