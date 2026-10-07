module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Envelope
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
public import ReasLib.Topology.Specialization.Dimension

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsEnvelope

/-- Envelopehood is stable under arbitrary base change of schemes. -/
instance isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange (@AlgebraicGeometry.IsEnvelope) := sorry

/-- If two schemes are locally of finite type over a universally catenary scheme with a
dimension function, then base change along a morphism over that scheme preserves envelopes. -/
theorem pullback_of_locallyOfFiniteType {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X X' : Over S)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    (g : X' ⟶ X) {Y : Scheme.{u}} (f : Y ⟶ X.left) [IsEnvelope f] :
    IsEnvelope (Limits.pullback.snd f g.left) := sorry

end AlgebraicGeometry.IsEnvelope
