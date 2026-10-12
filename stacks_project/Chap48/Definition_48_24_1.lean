/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 48.24.1: a scheme is Gorenstein if it is locally Noetherian and every one of its
local rings is Gorenstein. -/
@[stacks 0AWW] #check
  (AlgebraicGeometry.Scheme.Gorenstein : AlgebraicGeometry.Scheme.{u} → Prop)

#check
  (AlgebraicGeometry.Scheme.gorenstein_iff :
    (X : AlgebraicGeometry.Scheme.{u}) →
      AlgebraicGeometry.Scheme.Gorenstein X ↔
        AlgebraicGeometry.IsLocallyNoetherian X ∧
          ∀ x : X, IsGorensteinLocalRing (X.presheaf.stalk x))
