module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced
import StacksCheckRecall

@[expose] public section

universe u

/-!
# Definition 33.6.1 (035V): canonical geometric-reducedness owners.

The pointwise and field-extension APIs are owned by `SchemeOverField` in
`ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced`.
-/

/- Definition 33.6.1 (1): pointwise geometric reducedness. -/
@[stacks 035V] #check
  (AlgebraicGeometry.SchemeOverField.geometricallyReducedAt :
    {k : Type u} → [Field k] →
      (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))) → X.left → Prop)

/- Definition 33.6.1 (2): geometric reducedness over the base field. -/
@[stacks 035V] #check
  (AlgebraicGeometry.SchemeOverField.geometricallyReduced :
    {k : Type u} → [Field k] →
      CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) → Prop)
