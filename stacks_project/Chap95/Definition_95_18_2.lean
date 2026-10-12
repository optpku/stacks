/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import stacks_project.Chap95.Lemma_95_18_1
import StacksCheckRecall

/-!
# Definition 95.18.2

The degree `d` finite Hilbert stack `H_d(X/Y)` of a 1-morphism of stacks in
groupoids over `(Sch/S)_fppf`, together with the specializations `H_d(X)` and
`H_d`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteHilbertStack
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

/- Definition 95.18.2 (1): the degree `d` finite Hilbert stack `H_d(X/Y)` of a
1-morphism `F : X ⟶ Y` of stacks in groupoids over `(Sch/S)_fppf`. -/
@[stacks 05WC]
#check stack

/-- The identity fibration on `(Sch/S)_fppf` is a stack in groupoids. -/
instance instIsStackInGroupoids_base {S : Scheme.{u}} :
    IsStack.InGroupoids (Scheme.fppfTopology.over S)
      (base.{u + 1, u, u + 1} (Over S)).p :=
  sorry

/-- Definition 95.18.2 (2): if `Y = S`, write `H_d(X)` for `H_d(X/S)`. -/
@[stacks 05WC]
abbrev ofStack {S : Scheme.{u}} (X : GroupoidsOver S)
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p] (d : ℕ) :
    StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  stack (baseProjection.{u + 1, u, u + 1} X) d

/-- `ofStack X d` is the finite Hilbert stack of the structure 1-morphism of `X`. -/
theorem ofStack_eq {S : Scheme.{u}} (X : GroupoidsOver S)
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p] (d : ℕ) :
    ofStack X d = stack (baseProjection.{u + 1, u, u + 1} X) d :=
  sorry

/-- The projection of `ofStack X d` is the forgetful functor of the structure
1-morphism. -/
theorem ofStack_p {S : Scheme.{u}} (X : GroupoidsOver S)
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p] (d : ℕ) :
    (ofStack X d).p = p (baseProjection.{u + 1, u, u + 1} X) d :=
  sorry

/-- Definition 95.18.2 (3): if `X = Y = S`, denote the stack by `H_d`. -/
@[stacks 05WC]
abbrev ofScheme (S : Scheme.{u}) (d : ℕ) :
    StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  stack (𝟙 (base.{u + 1, u, u + 1} (Over S))) d

/-- `ofScheme S d` is the finite Hilbert stack of the identity 1-morphism of `S`. -/
theorem ofScheme_eq (S : Scheme.{u}) (d : ℕ) :
    ofScheme S d = stack (𝟙 (base.{u + 1, u, u + 1} (Over S))) d :=
  sorry

/-- The projection of `ofScheme S d` is the forgetful functor of the identity
1-morphism of `S`. -/
theorem ofScheme_p (S : Scheme.{u}) (d : ℕ) :
    (ofScheme S d).p = p (𝟙 (base.{u + 1, u, u + 1} (Over S))) d :=
  sorry

end AlgebraicGeometry.FiniteHilbertStack
