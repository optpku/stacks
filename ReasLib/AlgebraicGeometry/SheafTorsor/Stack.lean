/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.SheafTorsor.Category
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.ObjectProperty.Small

/-!
# The stack of torsors under an fppf sheaf of groups

The projection from restricted torsors to schemes over the base is a stack in
groupoids with essentially small fibers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SheafTorsors

variable {S : Scheme.{u}}

/-- The projection from torsors under a restricted fppf sheaf of groups is a stack
in groupoids on the fppf site of schemes over the base. -/
instance isStackInGroupoids (𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (forget 𝒢) := sorry

/-- The fiber of the torsor projection over a scheme has a set of isomorphism
class representatives in the universe of group sections. -/
instance fibers_essentiallySmall (𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u})
    (U : Over S) :
    ObjectProperty.EssentiallySmall.{u}
      (⊤ : ObjectProperty ((forget 𝒢).Fiber U)) := sorry

/-- The torsor projection is a stack in groupoids with essentially small fibers. -/
theorem isStackWithSmallFibers (𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (forget 𝒢) ∧
      ∀ U : Over S, ObjectProperty.EssentiallySmall.{u}
        (⊤ : ObjectProperty ((forget 𝒢).Fiber U)) :=
  ⟨isStackInGroupoids 𝒢, fibers_essentiallySmall 𝒢⟩

end AlgebraicGeometry.SheafTorsors
