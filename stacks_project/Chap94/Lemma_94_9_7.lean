/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# Base change of morphisms representable by algebraic spaces

Relative representability by algebraic spaces is stable under 2-fibre-product
base change of 1-morphisms of groupoid fibrations over `(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Lemma 94.9.7: let `S` be an object of `Sch_fppf`. Let `X`, `Y`, `Z` be
categories fibred in groupoids over `(Sch/S)_fppf`. If `f : X ⟶ Y` is a
1-morphism representable by algebraic spaces and `g : Z ⟶ Y` is any
1-morphism, then the base change `TwoFibreProduct.fst g f` is representable
by algebraic spaces. -/
@[stacks 0302]
theorem relativelyRepresentableByAlgebraicSpaces.pullback_fst
    {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    relativelyRepresentableByAlgebraicSpaces
      (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f) := sorry

end AlgebraicGeometry
