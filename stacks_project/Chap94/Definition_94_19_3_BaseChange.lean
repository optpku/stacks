/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Pullback.Pseudofunctor
public import stacks_project.Chap94.Definition_94_12_3_AlgebraicStacks

/-!
# Change of base of algebraic stacks

A morphism `g : S ⟶ S'` of schemes induces the localization functor
`j = Over.map g : Over S ⥤ Over S'`. The change of base of an algebraic stack
`X'` over `S'` is the pullback of the groupoid fibration `X'` along `j`. Its
total category is the 2-fibre product
`(Sch/S)_fppf ×_{(Sch/S')_fppf} X'`, and its structure morphism is the first
projection to `(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry

namespace AlgebraicStack

/-- The change of base of an algebraic stack `X'` over `S'` along a morphism
`g : S ⟶ S'` of the big fppf site. This is the groupoid fibration over `Over S`
obtained by pulling `X'` back along the localization functor `Over.map g`. -/
def baseChange {S S' : Scheme.{u}} (g : S ⟶ S') (X' : GroupoidsOver S')
    [AlgebraicStack X'] : GroupoidsOver S :=
  (FiberedCategoryOver.Groupoids.pullback.{u + 1, u + 1, u + 1, u, u, u}
    (Over.map g) X' : GroupoidsOver S)

/-- Unfolding `baseChange g X'` recovers the groupoid-fibred pullback along
`Over.map g`. -/
@[simp]
theorem baseChange_eq {S S' : Scheme.{u}} (g : S ⟶ S') (X' : GroupoidsOver S')
    [AlgebraicStack X'] :
    baseChange g X' =
      FiberedCategoryOver.Groupoids.pullback.{u + 1, u + 1, u + 1, u, u, u}
        (Over.map g) X' := sorry

/-- The total category of the change of base is the 2-fibre product of
`Over.map g` with the structure morphism of `X'`. -/
@[simp]
theorem baseChange_total {S S' : Scheme.{u}} (g : S ⟶ S') (X' : GroupoidsOver S')
    [AlgebraicStack X'] :
    (baseChange g X').total = CategoricalPullback (Over.map g) X'.p := sorry

/-- The structure morphism of the change of base is the first projection of the
2-fibre product onto `(Sch/S)_fppf`. -/
@[simp]
theorem baseChange_p {S S' : Scheme.{u}} (g : S ⟶ S') (X' : GroupoidsOver S')
    [AlgebraicStack X'] :
    (baseChange g X').p = CategoricalPullback.π₁ (Over.map g) X'.p := sorry

/-- The change of base of an algebraic stack over `S'` is an algebraic stack
over `S`. -/
instance instBaseChange {S S' : Scheme.{u}} (g : S ⟶ S') (X' : GroupoidsOver S')
    [AlgebraicStack X'] : AlgebraicStack (baseChange g X') := sorry

/-- Source reading of change of base: the underlying category is the 2-fibre
product `(Sch/S)_fppf ×_{(Sch/S')_fppf} X'`, and the structure morphism is the
first projection to `(Sch/S)_fppf`. -/
theorem baseChange_spec {S S' : Scheme.{u}} (g : S ⟶ S') (X' : GroupoidsOver S')
    [AlgebraicStack X'] :
    (baseChange g X').total = CategoricalPullback (Over.map g) X'.p ∧
      (baseChange g X').p = CategoricalPullback.π₁ (Over.map g) X'.p := sorry

end AlgebraicStack

namespace AlgebraicStacks

/-- Package the change of base of an object of the 2-category of algebraic
stacks over `S'` as an object of the 2-category of algebraic stacks over `S`. -/
def baseChange {S S' : Scheme.{u}} (g : S ⟶ S') (X' : AlgebraicStacks S') :
    AlgebraicStacks S :=
  of (AlgebraicStack.baseChange g (toGroupoids X'))

/-- Packaging change of base in `AlgebraicStacks` forgets to
`AlgebraicStack.baseChange` on the underlying groupoid fibrations. -/
theorem baseChange_toGroupoids {S S' : Scheme.{u}} (g : S ⟶ S')
    (X' : AlgebraicStacks S') :
    toGroupoids (baseChange g X') =
      AlgebraicStack.baseChange g (toGroupoids X') := sorry

end AlgebraicStacks

end AlgebraicGeometry
