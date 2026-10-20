/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.Topology.Sheaves.Stalks
public import ReasLib.Topology.Sheaves.Pointwise.Product

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat

noncomputable section

universe u

namespace TopCat.Presheaf.PointwiseProduct

/-- The pointwise product presheaf of abelian groups is a sheaf. -/
theorem isSheaf_addCommGrp {X : TopCat.{u}} (A : X → AddCommGrpCat.{u}) :
    (presheaf A).IsSheaf := sorry

/-- The indiscrete two-point topological space. -/
abbrev twoPointTrivial : TopCat.{0} := trivial.obj (Fin 2)

/-- The constant family of integer additive commutative groups on the indiscrete two-point space. -/
def constantInt : twoPointTrivial → AddCommGrpCat.{0} :=
  fun _ ↦ AddCommGrpCat.of ℤ

/-- The stalk of the pointwise product sheaf is not isomorphic to its integer fibre on the
indiscrete two-point space. -/
theorem not_isIsomorphic_stalk (x : twoPointTrivial) :
    ¬ IsIsomorphic ((presheaf constantInt).stalk x) (constantInt x) := sorry

end TopCat.Presheaf.PointwiseProduct

end

end
