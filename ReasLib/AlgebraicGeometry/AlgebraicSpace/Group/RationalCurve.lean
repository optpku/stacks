/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ConstantMorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Over

/-!
# Rational curves in group algebraic spaces

Every morphism from the projective line over a field to a separated group
algebraic space locally of finite type over that field is constant.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- A morphism from the projective line over a field to a separated group algebraic space locally
of finite type over that field factors through the base. -/
theorem isConstant_hom_projectiveLine {k : Type u} [Field k]
    (G : GroupAlgebraicSpace (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
    [AlgebraicSpace.IsSeparated G.X.left]
    [AlgebraicSpace.LocallyOfFiniteType (SchemeRealization.toBase G.X.left)]
    (f : ofOver (ProjectiveSpace.schemeOver k 1) ⟶ G.X.left) :
    AlgebraicSpace.IsConstant f :=
  sorry

/-- There is no nonconstant morphism from the projective line over a field to a separated group
algebraic space locally of finite type over that field. -/
theorem not_exists_not_isConstant_hom_projectiveLine {k : Type u} [Field k]
    (G : GroupAlgebraicSpace (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
    [AlgebraicSpace.IsSeparated G.X.left]
    [AlgebraicSpace.LocallyOfFiniteType (SchemeRealization.toBase G.X.left)] :
    ¬ ∃ f : ofOver (ProjectiveSpace.schemeOver k 1) ⟶ G.X.left,
        ¬ AlgebraicSpace.IsConstant f :=
  sorry

end AlgebraicGeometry.GroupAlgebraicSpace
