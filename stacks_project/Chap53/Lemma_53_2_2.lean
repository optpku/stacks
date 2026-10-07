module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.RationalMap

public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Curve

/- Lemma 53.2.2 -/
@[stacks 0BXZ] #check (AlgebraicGeometry.Curve.existsUnique_hom_of_rationalMap :
    ∀ {k : Type u} [Field k] (X Y : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.Curve X] (hX : X.left.isNormal) [AlgebraicGeometry.Variety Y]
      [AlgebraicGeometry.IsProper Y.hom] (φ : X.left ⤏ Y.left)
      [φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))],
      ∃! f : X ⟶ Y, f.left.toRationalMap = φ)

end AlgebraicGeometry.Curve
