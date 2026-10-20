module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Restrictions of formally unramified morphisms

Formally unramified scheme morphisms remain formally unramified after restriction to compatible
open subschemes of their source and target.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FormallyUnramified

/-- Formally unramified scheme morphisms remain formally unramified after restriction to open
subschemes of their source and target. -/
instance resLE {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) (V : S.Opens)
    (e : U ≤ f ⁻¹ᵁ V) [FormallyUnramified f] : FormallyUnramified (f.resLE V U e) := sorry

end AlgebraicGeometry.FormallyUnramified
