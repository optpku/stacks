module

public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap88.«88_27_0_1_Completion»

/-!
# Algebraization of affine rig-étale morphisms into a completion

A rig-étale morphism from a Noetherian affine formal algebraic space into the
completion of a Noetherian affine algebraic space along a closed subset
algebraizes to an affine finite-type morphism étale off that closed subset.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace completionAlong

/-- Lemma 88.25.1 (1): If `T` is closed in a Noetherian affine algebraic space
`X` and `g : W ⟶ completionAlong X T` is a rig-étale morphism from a Noetherian
affine formal algebraic space `W`, then there exist an affine algebraic space
`X'` and a finite-type morphism `f : X' ⟶ X` étale over the open complement of
`T` together with an isomorphism
`completionAlong X' (T.preimage (Points.continuous_map f)) ≅ W` compatible with
`map f T` and `g`. -/
@[stacks 0AR4]
theorem exists_affineAlgebraize {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsAffine X] [IsNoetherian X] (T : Closeds (Points X))
    {W : (Over S)ᵒᵖ ⥤ Type u} [FormalAlgebraicSpace.IsFormalAlgebraicSpace W]
    [FormalAlgebraicSpace.IsAffine W] [FormalAlgebraicSpace.IsNoetherianAffine W]
    (g : W ⟶ completionAlong X T) [FormalAlgebraicSpace.RigEtale g] :
    ∃ (X' : AlgebraicSpace S) (_ : IsAffine X') (f : X' ⟶ X) (_ : FiniteType f)
      (_ : Etale (openInverseImageTo f (openComplementι X T)))
      (e : completionAlong X' (T.preimage (Points.continuous_map f)) ≅ W),
      e.hom ≫ g = map f T :=
  sorry

/-- Lemma 88.25.1 (2): In the situation of `exists_affineAlgebraize`, if `g` is
étale as a morphism of formal algebraic spaces, then any such algebraizing
morphism `f` is étale. -/
@[stacks 0AR4]
theorem etale_of_etale {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    [IsAffine X] [IsNoetherian X] [IsAffine X'] (T : Closeds (Points X))
    (f : X' ⟶ X) [FiniteType f]
    (hf : Etale (openInverseImageTo f (openComplementι X T)))
    {W : (Over S)ᵒᵖ ⥤ Type u} [FormalAlgebraicSpace.IsFormalAlgebraicSpace W]
    [FormalAlgebraicSpace.IsAffine W] [FormalAlgebraicSpace.IsNoetherianAffine W]
    (g : W ⟶ completionAlong X T) [FormalAlgebraicSpace.RigEtale g]
    [FormalAlgebraicSpace.Etale g]
    (e : completionAlong X' (T.preimage (Points.continuous_map f)) ≅ W)
    (he : e.hom ≫ g = map f T) : Etale f :=
  sorry

end completionAlong

end AlgebraicGeometry.AlgebraicSpace
