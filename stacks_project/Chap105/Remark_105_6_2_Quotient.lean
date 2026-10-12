/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import stacks_project.Chap78.Lemma_78_15_1_Action
public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap105.Remark_105_6_2_Weierstrass

/-!
# Global quotient stacks and the Weierstrass presentation of `M₁₁`

A global quotient stack is a stack equivalent to `[X / G]` for a group algebraic space `G`
acting on an algebraic space coming from a scheme. The Weierstrass action of `H` on `W` yields
the quotient stack `[W / H]`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CartesianMonoidalCategory MonoidalCategory FiberedCategoryOver.Groupoids
open scoped Bicategory CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic stack is a global quotient stack if it is equivalent to `[X / G]` for a group
algebraic space `G` acting on an algebraic space `X` coming from a scheme. -/
class IsGlobalQuotientStack {S : Scheme.{u}} (X : GroupoidsOver S) : Prop where
  /-- There is a group algebraic space acting on a scheme whose quotient stack is equivalent to
  `X`. -/
  exists_action :
    ∃ (B : AlgebraicSpace S) (G : GroupAlgebraicSpace B)
      (Y : GroupAlgebraicSpace.Action G) (T : Over S),
      Y.X.left = ofOver T ∧
        ∃ (f : (GroupoidAlgebraicSpace.ofAction G Y).quotientStack ⟶ X),
          (toBasedFunctor f).IsEquivalence

namespace IsGlobalQuotientStack

/-- A stack is a global quotient stack if and only if it is equivalent to the quotient stack of
a group algebraic space acting on a scheme. -/
theorem iff {S : Scheme.{u}} (X : GroupoidsOver S) :
    IsGlobalQuotientStack X ↔
      ∃ (B : AlgebraicSpace S) (G : GroupAlgebraicSpace B)
        (Y : GroupAlgebraicSpace.Action G) (T : Over S),
        Y.X.left = ofOver T ∧
          ∃ (f : (GroupoidAlgebraicSpace.ofAction G Y).quotientStack ⟶ X),
            (toBasedFunctor f).IsEquivalence :=
  sorry

end IsGlobalQuotientStack

/-- The identity on an action quotient stack is an equivalence. -/
instance ofAction_id_isEquivalence {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (Y : GroupAlgebraicSpace.Action G) :
    (toBasedFunctor (𝟙 (GroupoidAlgebraicSpace.ofAction G Y).quotientStack)).IsEquivalence :=
  sorry

/-- The quotient stack of a group algebraic space acting on an algebraic space is a global
quotient stack when the acted-on space comes from a scheme `T`. -/
theorem isGlobalQuotientStack_ofAction {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (Y : GroupAlgebraicSpace.Action G)
    (T : Over S) (hY : Y.X.left = ofOver T) :
    IsGlobalQuotientStack (GroupoidAlgebraicSpace.ofAction G Y).quotientStack :=
  sorry

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry.AlgebraicStack.WeierstrassQuotient

/-- The action groupoid of `H` acting on `W`. -/
def groupoid : GroupoidAlgebraicSpace terminalSpace :=
  GroupoidAlgebraicSpace.ofAction group action

/-- The object space of the action groupoid is the Weierstrass scheme. -/
theorem groupoid_U : groupoid.U = schemeAsOver :=
  sorry

/-- The arrow space of the action groupoid is `H × W`. -/
theorem groupoid_R : groupoid.R = (group.X ⊗ schemeAsOver) :=
  sorry

/-- The quotient stack `[W / H]` of the Weierstrass action. -/
def stack : GroupoidsOver base :=
  groupoid.quotientStack

/-- `stack` is the quotient stack of the Weierstrass action groupoid. -/
theorem stack_eq : stack = groupoid.quotientStack :=
  sorry

/-- The atlas `W ⟶ [W / H]`. -/
def atlas : (AlgebraicSpace.ofOver scheme).toGroupoids ⟶ stack :=
  groupoid.atlas

/-- `atlas` is the atlas of the Weierstrass action groupoid. -/
theorem atlas_eq : atlas = groupoid.atlas :=
  sorry

/-- The Weierstrass quotient stack `[W / H]` is a global quotient stack. -/
instance instIsGlobalQuotientStack : IsGlobalQuotientStack stack :=
  isGlobalQuotientStack_ofAction group action scheme action_left_eq

end AlgebraicGeometry.AlgebraicStack.WeierstrassQuotient
