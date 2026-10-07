module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversallyInjective.GenericPoints

/-!
# Open immersions from generic-point criteria

This file records a criterion for an étale separated morphism to be an open immersion in
terms of its action on generic points and their residue fields.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsOpenImmersion

/-- An étale separated morphism which induces residue-field isomorphisms at the generic
points of its source and is injective on those generic points is an open immersion. -/
theorem of_etale_of_isSeparated_of_genericPoints {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Etale f] [IsSeparated f]
    (hκ : ∀ ξ : X, ξ ∈ genericPoints X → IsIso (f.residueFieldMap ξ))
    (hgen : Set.InjOn f.base (genericPoints X)) :
    IsOpenImmersion f := sorry

end AlgebraicGeometry.IsOpenImmersion
