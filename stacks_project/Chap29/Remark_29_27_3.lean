/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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
