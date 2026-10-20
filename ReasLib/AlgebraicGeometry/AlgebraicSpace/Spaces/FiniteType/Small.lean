/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.FiniteType
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.ObjectProperty.Small

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.FiniteType

/-- Each fiber of the finite-type algebraic-space projection is essentially small. -/
instance fibers_essentiallySmall (S : Scheme.{u}) (U : Over S) :
    ObjectProperty.EssentiallySmall.{u} (⊤ : ObjectProperty ((p S).Fiber U)) := sorry

/-- The finite-type algebraic-space stack admits an essentially surjective full
subcategory whose restricted projection is an fppf stack with small fibers. -/
@[stacks 04UE]
theorem exists_smallSubcategory (S : Scheme.{u}) :
    ∃ P : ObjectProperty (stack S).total,
      P.ι.EssSurj ∧
        IsStack.OnSite (Scheme.fppfTopology.over S) (P.ι ⋙ (stack S).p) ∧
        ∀ U : Over S, Small.{u} ((P.ι ⋙ (stack S).p).Fiber U) := sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.FiniteType
