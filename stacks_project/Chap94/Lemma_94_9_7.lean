module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.BaseChange
import StacksCheckRecall

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

/- Lemma 94.9.7: let `S` be an object of `Sch_fppf`. Let `X`, `Y`, `Z` be
categories fibred in groupoids over `(Sch/S)_fppf`. If `f : X ⟶ Y` is a
1-morphism representable by algebraic spaces and `g : Z ⟶ Y` is any
1-morphism, then the base change `TwoFibreProduct.fst g f` is representable
by algebraic spaces. -/
@[stacks 0302] #check
  (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.pullback_fst :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Z ⟶ Y),
      relativelyRepresentableByAlgebraicSpaces f →
        relativelyRepresentableByAlgebraicSpaces
          (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f))

end AlgebraicGeometry
