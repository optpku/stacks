module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- The product map over a scheme and the second projections form a cartesian square
of underlying schemes. -/
theorem overProdMapSndIsPullback {S : Scheme.{u}} (X : Over S) {Y Z : Over S}
    (g : Y ⟶ Z) :
    IsPullback (Limits.prod.snd : X ⨯ Y ⟶ Y).left
      (Limits.prod.map (𝟙 X) g : X ⨯ Y ⟶ X ⨯ Z).left g.left
      (Limits.prod.snd : X ⨯ Z ⟶ Z).left := sorry

end AlgebraicGeometry.Scheme
