module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Prorepresentable
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber

/-!
# Endomorphisms of prorepresentable functors with invertible differential

If `U : ArtinianLocalAlgCat Λ k ⥤ Type u` is prorepresentable, an endomorphism
whose dual-number component is bijective is itself an isomorphism.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- An endomorphism of a prorepresentable functor is an isomorphism if its component
at the dual-number algebra is bijective. This component is the induced map on the
tangent space of the functor. -/
@[stacks 06KP]
theorem isIso_of_bijective_tangentSpace {U : ArtinianLocalAlgCat Λ k ⥤ Type u}
    [IsProrepresentable U] (φ : U ⟶ U)
    (hφ : Function.Bijective (φ.app (ArtinianLocalAlgCat.dualNumber Λ k))) :
    IsIso φ := sorry

end CategoryTheory.Functor
