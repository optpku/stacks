module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallySmooth

/-!
# Restrictions of formally smooth morphisms

Formally smooth scheme morphisms remain formally smooth after restriction to compatible open
subschemes of their source and target.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FormallySmooth

/-- Formally smooth scheme morphisms remain formally smooth after restriction to open
subschemes of their source and target. -/
instance resLE {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) (V : S.Opens)
    (e : U ≤ f ⁻¹ᵁ V) [FormallySmooth f] : FormallySmooth (f.resLE V U e) := sorry

end AlgebraicGeometry.FormallySmooth
