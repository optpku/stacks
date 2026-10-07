module

public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Lemma_67_38_8_Unramified
public import stacks_project.Chap66.Lemma_66_16_4_Etale

/-!
# Locally finitely presented, flat, unramified morphisms of algebraic spaces
are étale
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.39.12: A locally finitely presented, flat, unramified morphism of
algebraic spaces is étale. -/
@[stacks 06LU]
instance etale_of_locallyOfFinitePresentation_of_flat_of_unramified
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [Flat f] [Unramified f] : Etale f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
