/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommAlgCat.Limits
public import ReasLib.AlgebraicGeometry.RingedSpace.Definition
public import ReasLib.Topology.Sheaves.ContinuousFunctions.Real
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ringed spaces of continuous real-valued functions

This file bundles the sheaf of continuous real-valued functions on a topological space as a ringed
space.  The algebra-valued sheaf remains the canonical construction; `ringedSpace` only forgets its
`ℝ`-algebra structure to a commutative-ring-valued sheaf.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ContinuousFunctions.Real

/-- A topological space equipped with its sheaf of continuous real-valued functions. -/
@[stacks 01BL "continuous real-valued functions"]
noncomputable def ringedSpace (X : TopCat.{u}) : RingedSpace.{u} :=
  { carrier := X
    presheaf :=
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ (CommAlgCat.{u} ℝ) CommRingCat)).obj
          (TopCat.ContinuousFunctions.Real.sheaf X)).1
    IsSheaf :=
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ (CommAlgCat.{u} ℝ) CommRingCat)).obj
          (TopCat.ContinuousFunctions.Real.sheaf X)).2 }

/-- The underlying topological space of `ringedSpace X` is definitionally `X`. -/
@[simp]
theorem carrier_ringedSpace (X : TopCat.{u}) :
    (ringedSpace X).carrier = X := sorry

end AlgebraicGeometry.RingedSpace.ContinuousFunctions.Real
