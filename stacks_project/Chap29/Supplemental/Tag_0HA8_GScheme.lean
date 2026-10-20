module

public import ReasLib.AlgebraicGeometry.Scheme.GScheme

/-!
# G-schemes

A scheme is a G-scheme when the G-ring property holds on an affine open neighbourhood of every
point. This is independent of group actions: a G-scheme in this sense is not a scheme equipped
with an action of a finite group or group scheme.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

#check (AlgebraicGeometry.Scheme.gScheme_iff :
  ∀ X : Scheme.{u},
    X.GScheme ↔ ∀ x : X, ∃ U : X.affineOpens, x ∈ U ∧ IsGRing (Γ(X, U)))
