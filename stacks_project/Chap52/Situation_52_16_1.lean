/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization
import StacksCheckRecall

@[expose] public section

universe u

/- Situation 52.16.1: a Noetherian ring `A` together with ideals `I ⊆ a` used to form
`X = Spec(A)`, `Y = Spec(A ⧸ I)`, `Z = Spec(A ⧸ a)`, and the open complement
`U = X \ Z`. -/
@[stacks 0EHC]
#check (AlgebraicGeometry.AffineAlgebraizationSetup :
  (A : Type u) → [CommRing A] → [IsNoetherianRing A] → Type u)
