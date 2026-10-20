module

public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.EtaleLocal
public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.StalkMap

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Germ.MorphismProperty

/-- The property that a morphism of scheme germs induces a flat map on the
distinguished stalks. -/
def flat : CategoryTheory.MorphismProperty Germ.{u} :=
  stalkwise RingHom.Flat

/-- A germ morphism satisfies `flat` exactly when its distinguished stalk map is flat. -/
theorem flat_iff {X Y : Germ.{u}} (f : X ⟶ Y) :
    flat f ↔ RingHom.Flat f.stalkMap.hom := sorry

/-- Flatness of the induced map on distinguished stalks is étale local on the
source-and-target for morphisms of scheme germs. -/
theorem flat_isEtaleLocal : IsEtaleLocal flat := sorry

end AlgebraicGeometry.Scheme.Germ.MorphismProperty
