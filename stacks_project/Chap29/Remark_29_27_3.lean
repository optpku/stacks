module

import StacksCheckRecall
import Mathlib.AlgebraicGeometry.Morphisms.Flat

universe u

/- Remark 29.27.3: the generic-flatness results above are a first step toward more refined
flattening techniques for morphisms of schemes. The Raynaud–Gruson article `[GruRay]` contains
many results in this direction. -/
@[stacks 052C] #check
  (AlgebraicGeometry.Flat :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}}, (X ⟶ Y) → Prop)
