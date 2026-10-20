module

public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationFunctor.Rigidity
import StacksCheckRecall

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

/- Lemma 90.18.1: A smooth morphism between deformation functors with bijective
tangent map is an isomorphism. -/
@[stacks 06JL] #check
  (CategoryTheory.Functor.isIso_of_isSmooth_of_bijective_tangentSpace :
    ∀ {F G : ArtinianLocalAlgCat Λ k ⥤ Type v}
      [CategoryTheory.Functor.IsDeformationFunctor F]
      [CategoryTheory.Functor.IsDeformationFunctor G] (φ : F ⟶ G)
      [CategoryTheory.NatTrans.IsSmooth φ],
      Function.Bijective (φ.app (ArtinianLocalAlgCat.dualNumber Λ k)) → IsIso φ)
