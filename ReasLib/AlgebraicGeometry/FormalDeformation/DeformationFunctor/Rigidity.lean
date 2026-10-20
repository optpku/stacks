module

public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationFunctor
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothFunctor
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber

/-!
# Smooth morphisms of deformation functors with invertible differential

A smooth morphism of deformation functors whose dual-number component is bijective
is itself an isomorphism.
-/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- A smooth morphism between deformation functors is an isomorphism if its component
at the dual-number algebra is bijective. This component is the induced map on their
tangent spaces. -/
@[stacks 06JL]
theorem isIso_of_isSmooth_of_bijective_tangentSpace
    {F G : ArtinianLocalAlgCat Λ k ⥤ Type v}
    [IsDeformationFunctor F] [IsDeformationFunctor G] (φ : F ⟶ G)
    [NatTrans.IsSmooth φ]
    (hφ : Function.Bijective (φ.app (ArtinianLocalAlgCat.dualNumber Λ k))) :
    IsIso φ := sorry

end CategoryTheory.Functor
