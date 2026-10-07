module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.IntersectionDimension
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 43.13.4: every irreducible component of the scheme-theoretic intersection of
closed subvarieties `V` and `W` in a nonsingular variety `X` has dimension at least
`dim(V) + dim(W) - dim(X)`. -/
@[stacks 0AZP] #check
  (AlgebraicGeometry.SchemeOverField.componentDimension_lowerBound_of_intersection :
    {k : Type u} → [Field k] → [IsAlgClosed k] →
    (X : SchemeOverField k) → [Variety X] → [Scheme.Regular X.left] →
    (V W : X.left.IdealSheafData) →
    [Variety (Over.mk (V.subschemeι ≫ X.hom))] →
    [Variety (Over.mk (W.subschemeι ≫ X.hom))] →
    (r s : ℕ) →
    topologicalKrullDim V.subscheme = (r : WithBot ℕ∞) →
    topologicalKrullDim W.subscheme = (s : WithBot ℕ∞) →
    (Z : irreducibleComponents (V ⊔ W).subscheme) →
    ((r + s - baseFieldTrdegAt X (genericPoint X.left) : ℕ) : WithBot ℕ∞) ≤
      topologicalKrullDim Z)

end AlgebraicGeometry.SchemeOverField
