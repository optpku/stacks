module

import Mathlib.AlgebraicGeometry.Birational.RationalMap
import StacksCheckRecall

open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

/- Definition 29.49.8: a rational map `φ : X.RationalMap Y` is defined at `x : X` exactly when
some representative of `φ` has domain containing `x`; `φ.domain` is the open set of all such
points. -/
@[stacks 0A1X] #check
  (RationalMap.mem_domain :
    ∀ {X Y : Scheme.{u}} {φ : X.RationalMap Y} {x : X},
      x ∈ φ.domain ↔ ∃ g : X.PartialMap Y, x ∈ g.domain ∧ g.toRationalMap = φ)

end AlgebraicGeometry.Scheme
