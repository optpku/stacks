/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap95.Proposition_95_15_3_Comparison
public import stacks_project.Chap95.Proposition_95_15_3_Quotient

/-!
# Proposition 95.15.3

In Situation 95.15.1 there is a canonical equivalence `[X/G] ⟶ [[X/G]]` of
stacks in groupoids over `(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupAlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace
open AlgebraicGeometry.QuotientStack
open scoped Bicategory

noncomputable section

universe u

/-- Proposition 95.15.3 (1): In Situation 95.15.1 there exists a canonical
1-morphism `[X/G] ⟶ [[X/G]]` of stacks in groupoids over `(Sch/S)_fppf`,
where `[X/G]` is `(ofAction G X).quotientStack` and `[[X/G]]` is
`GroupAction.stack G X`. -/
@[stacks 04WM]
noncomputable abbrev equivalent {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : Action G) :
    CartesianBasedFunctor (quotientStack (ofAction G X)).p
      (GroupAction.forget G X) :=
  GroupAction.equivalent G X

/-- Proposition 95.15.3 (2): the comparison `[X/G] ⟶ [[X/G]]` is an equivalence of
stacks in groupoids over `(Sch/S)_fppf`. -/
@[stacks 04WM, instance]
instance equivalent_isEquivalence {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : Action G) :
    (equivalent G X).toBasedFunctor.IsEquivalence :=
  GroupAction.equivalent_isEquivalence G X
