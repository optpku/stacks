module

public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_36_4_Syntomic

/-!
# Syntomic morphisms of algebraic spaces are locally of finite presentation
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.36.5: A syntomic morphism is locally of finite presentation. -/
@[stacks 0DEY]
instance locallyOfFinitePresentation_of_syntomic {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Syntomic f] :
    LocallyOfFinitePresentation f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
