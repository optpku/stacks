/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap95.Lemma_95_18_1_Category

/-!
# Lemma 95.18.1

The category `H_d(X/Y)` of degree `d` finite Hilbert lifts along a 1-morphism
of stacks in groupoids, with its forgetful functor `p`, is a stack in groupoids
over `(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}

/-- Lemma 95.18.1: the category `H_d(X/Y)` endowed with the forgetful functor `p`
defines a stack in groupoids over `(Sch/S)_fppf`. -/
@[stacks 05WB]
instance isStackInGroupoids
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (F : X ⟶ Y) (d : ℕ) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (p F d) := sorry

/-- The stack in groupoids of degree `d` finite Hilbert lifts along `F`. -/
def stack
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (F : X ⟶ Y) (d : ℕ) :
    StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  StackOver.Groupoids.ofProjection (Scheme.fppfTopology.over S) (p F d)

/-- The projection of `stack` is the forgetful functor `p`. -/
theorem stack_p
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (F : X ⟶ Y) (d : ℕ) :
    (stack F d).p = p F d := sorry

end AlgebraicGeometry.FiniteHilbertStack
