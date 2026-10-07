module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.Subgroup

universe u

/-
Definition 39.4.3 (1): a closed subgroup scheme of a group scheme `G` over `S`
is a group object over `S` whose inclusion into `G` is a closed immersion.
-/
@[stacks 047D] #check (AlgebraicGeometry.Scheme.ClosedSubgroup :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : CategoryTheory.Over S)
    [CategoryTheory.GrpObj G], Type (u + 1))

/-
Definition 39.4.3 (2): an open subgroup scheme of a group scheme `G` over `S`
is a group object over `S` whose inclusion into `G` is an open immersion.
-/
@[stacks 047D] #check (AlgebraicGeometry.Scheme.OpenSubgroup :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : CategoryTheory.Over S)
    [CategoryTheory.GrpObj G], Type (u + 1))
