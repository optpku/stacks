module

public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation

/-!
# Étale morphisms of algebraic spaces are locally of finite presentation
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.39.8: An étale morphism of algebraic spaces is locally of finite presentation. -/
@[stacks 0468]
instance locallyOfFinitePresentation_of_etale {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] : LocallyOfFinitePresentation f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
