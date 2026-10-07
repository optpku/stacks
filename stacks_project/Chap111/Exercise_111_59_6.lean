module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.GeometricGenus.Product
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

/- Exercise 111.59.6: over an algebraically closed field `k`, with `3 ≤ g`, if
`X` and `X'` are smooth projective curves of genus `g` and `g + 1`, and `Y` is a
curve with a closed immersion into `X ⨯ X'` whose projections to `X` and `X'`
are nonconstant, then the nonsingular projective model of `Y` has genus at least
`2 * g + 1`. -/
@[stacks 0DT5] #check
  (AlgebraicGeometry.Curve.nonsingularProjectiveModel_genus_ge :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] {g : ℕ}, 3 ≤ g →
      (X X' : SchemeOverField k) →
      [Curve X] → [Projective X.hom] → [Smooth X.hom] →
      [Curve X'] → [Projective X'.hom] → [Smooth X'.hom] →
      genus X = g → genus X' = g + 1 →
      (Y : SchemeOverField k) → [Curve Y] →
      (ι : Y ⟶ X ⨯ X') → [IsClosedImmersion ι.left] →
      (ι ≫ prod.fst).left.IsNonconstant →
      (ι ≫ prod.snd).left.IsNonconstant →
      (M : NonsingularProjectiveModel.WithIso Y) →
      2 * g + 1 ≤ M.genus)

#check
  (AlgebraicGeometry.Curve.geometricGenus_ge_two_mul_add_one :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] {g : ℕ}, 3 ≤ g →
      (X X' : SchemeOverField k) →
      [Curve X] → [Projective X.hom] → [Smooth X.hom] →
      [Curve X'] → [Projective X'.hom] → [Smooth X'.hom] →
      genus X = g → genus X' = g + 1 →
      (Y : SchemeOverField k) → [Curve Y] →
      (ι : Y ⟶ X ⨯ X') → [IsClosedImmersion ι.left] →
      (ι ≫ prod.fst).left.IsNonconstant →
      (ι ≫ prod.snd).left.IsNonconstant →
      2 * g + 1 ≤ geometricGenus Y)

end AlgebraicGeometry.Curve
