/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_10_1_DualNumber
public import stacks_project.Chap90.Definition_90_23_1_Smooth
public import stacks_project.Chap90.Remark_90_16_9_DeformationFunctor

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

/-- Lemma 90.18.1: if `F, G : ArtinianLocalAlgCat Λ k ⥤ Type v` are deformation
functors and `φ : F ⟶ G` is a smooth morphism such that `dφ : TF → TG` is an
isomorphism of tangent spaces, then `φ` is an isomorphism. Here `TF` is
`F.obj (ArtinianLocalAlgCat.dualNumber Λ k)` and `dφ` is the component
`φ.app (ArtinianLocalAlgCat.dualNumber Λ k)`. -/
@[stacks 06JL]
theorem isIso_of_isSmooth_of_bijective_tangentSpace
    {F G : ArtinianLocalAlgCat Λ k ⥤ Type v}
    [IsDeformationFunctor F] [IsDeformationFunctor G] (φ : F ⟶ G)
    [NatTrans.IsSmooth φ]
    (hφ : Function.Bijective (φ.app (ArtinianLocalAlgCat.dualNumber Λ k))) :
    IsIso φ := sorry

end CategoryTheory.Functor
