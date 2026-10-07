module

public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation

/-!
# Smooth morphisms of algebraic spaces are locally of finite presentation
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.37.5: A smooth morphism of algebraic spaces is locally of finite
presentation. -/
@[stacks 04AJ]
instance locallyOfFinitePresentation_of_smooth {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Smooth f] :
    LocallyOfFinitePresentation f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
