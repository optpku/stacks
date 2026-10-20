module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Cartesian

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- The product map `𝟙 X ⨯ g` and the second projections form a cartesian square. -/
theorem prodMapSndIsPullback (X : SchemeOverField k) {Y Z : SchemeOverField k}
    (g : Y ⟶ Z) :
    IsPullback (Limits.prod.snd : X ⨯ Y ⟶ Y).left
      (Limits.prod.map (𝟙 X) g : X ⨯ Y ⟶ X ⨯ Z).left g.left
      (Limits.prod.snd : X ⨯ Z ⟶ Z).left := sorry

end AlgebraicGeometry.SchemeOverField
