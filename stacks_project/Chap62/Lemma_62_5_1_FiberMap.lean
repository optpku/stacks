module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Comparison

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- The restriction-fibre comparison remains available to source-side consumers. -/
#check (AlgebraicGeometry.Scheme.Hom.resLEFiberMap :
  {X S : Scheme.{u}} → (f : X ⟶ S) → (U : X.Opens) → (V : S.Opens) →
    (hU : U ≤ f ⁻¹ᵁ V) → (s : V.toScheme) →
      (f.resLE V U hU).fiber s ⟶ f.fiber (V.ι s))
