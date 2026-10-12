/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.Subgroup.Factorization
public import stacks_project.Chap39.Lemma_39_4_4_Subgroup

universe u

open CategoryTheory

/- Lemma 39.4.4 (1): A closed subscheme `j : H ⟶ G` of a group scheme over `S`
is a closed subgroup scheme exactly when the unit, restricted multiplication, and inverse
of `G` factor through `H`. -/
@[stacks 0G8L] #check
  (AlgebraicGeometry.closedSubgroup_iff_factorization :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {H G : Over S}
      [GrpObj G] (j : H ⟶ G) [AlgebraicGeometry.IsClosedImmersion j.left],
      Nonempty (GrpObj.Restriction j) ↔ Nonempty (GrpObj.Factorization j))

/- Lemma 39.4.4 (2): An open subscheme `j : H ⟶ G` of a group scheme over `S`
is an open subgroup scheme exactly when the unit, restricted multiplication, and inverse
of `G` factor through `H`. -/
@[stacks 0G8L] #check
  (AlgebraicGeometry.openSubgroup_iff_factorization :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {H G : Over S}
      [GrpObj G] (j : H ⟶ G) [AlgebraicGeometry.IsOpenImmersion j.left],
      Nonempty (GrpObj.Restriction j) ↔ Nonempty (GrpObj.Factorization j))
