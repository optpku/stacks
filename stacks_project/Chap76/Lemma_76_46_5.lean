module

public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap76.Definition_76_46_1_PseudoCoherent

/-!
# Flat morphisms of algebraic spaces that are locally of finite presentation
are pseudo-coherent
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.46.5: A flat morphism of algebraic spaces which is locally of
finite presentation is pseudo-coherent. -/
@[stacks 06BV]
instance pseudoCoherent_of_flat_of_locallyOfFinitePresentation {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Flat f]
    [LocallyOfFinitePresentation f] : PseudoCoherent f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
