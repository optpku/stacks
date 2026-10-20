module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction

@[expose] public section

universe u

namespace CategoryTheory.ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S]

/-- A morphism into derived restriction of scalars transposes to a morphism out of derived
extension of scalars along the same ring homomorphism. -/
noncomputable def derivedExtensionRestrictionMap (σ : R →+* S)
    {K : DerivedCategory (ModuleCat.{u, u} R)}
    {L : DerivedCategory (ModuleCat.{u, u} S)}
    (comparison : K ⟶ (derivedRestrictionOfScalars σ).obj L) :
    (derivedExtensionOfScalars σ).obj K ⟶ L :=
  ((derivedExtensionRestrictionAdjunction σ).homEquiv K L).symm comparison

end CategoryTheory.ModuleCat
