/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.RelationFiniteFibre
import StacksCheckRecall

/-!
# Finite self-relation fibres over a point of an algebraic space

The existence of an étale scheme chart with finite self-relation fibre over a point
is equivalent to the same finiteness for every étale chart, to the existence of a
field-valued point with étale quasi-compact self-relation projections, and to the
existence of a monomorphism from the spectrum of a field in that point class.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 68.4.3. For a point of an algebraic space over a scheme, the existence
of an étale scheme chart and a pair above the point with finite self-relation fibre,
the universal version of this finiteness condition, a field-valued representative
with both self-relation projections étale and quasi-compact, and a monomorphic
field-valued representative are equivalent. -/
@[stacks 03JU] #check (AlgebraicGeometry.AlgebraicSpace.finiteRelationFibre_tfae :
  ∀ {S : Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)
    (x : AlgebraicGeometry.AlgebraicSpace.Points X),
    List.TFAE [AlgebraicGeometry.AlgebraicSpace.existsEtaleRelationFiniteFibre X x,
      AlgebraicGeometry.AlgebraicSpace.forallEtaleRelationFiniteFibre X x,
      AlgebraicGeometry.AlgebraicSpace.existsEtaleQuasiCompactFieldSelfRelation X x,
      AlgebraicGeometry.AlgebraicSpace.existsMonoFieldValuedPoint X x])
