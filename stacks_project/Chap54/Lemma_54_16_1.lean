module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ExceptionalCurve.Contraction

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsContraction

/- Lemma 54.16.1: every morphism that maps an exceptional curve of the first kind to one point
factors uniquely through any contraction of that curve. -/
@[stacks 0C5J] #check (AlgebraicGeometry.IsContraction.existsUnique_factor :
  ∀ {X X' Y : Scheme.{u}} [IsNoetherian X]
    {E : X.IdealSheafData} [IsExceptionalCurveFirstKind E]
    {b : X ⟶ X'} {x : closedPoints X'}, IsContraction E b x →
    (φ : X ⟶ Y) → (y : Y) → Set.MapsTo φ E.support ({y} : Set Y) →
      ∃! g : X' ⟶ Y, b ≫ g = φ)

end AlgebraicGeometry.IsContraction
