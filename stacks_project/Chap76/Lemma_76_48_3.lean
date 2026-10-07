module

public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap76.Definition_76_46_1_PseudoCoherent
public import stacks_project.Chap76.Definition_76_47_1_Perfect
public import stacks_project.Chap76.Definition_76_48_1_LocalCompleteIntersection

/-!
# Finiteness properties of local complete intersection morphisms of algebraic spaces

A local complete intersection morphism of algebraic spaces is locally of
finite presentation, pseudo-coherent, and perfect.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.48.3 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a local complete
intersection morphism of algebraic spaces over `S`. Then `f` is locally of
finite presentation. -/
@[stacks 06C6]
instance IsLocalCompleteIntersection.locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsLocalCompleteIntersection f] : LocallyOfFinitePresentation f :=
  sorry

/-- Lemma 76.48.3 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a local complete
intersection morphism of algebraic spaces over `S`. Then `f` is
pseudo-coherent. -/
@[stacks 06C6]
instance IsLocalCompleteIntersection.pseudoCoherent {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsLocalCompleteIntersection f] :
    PseudoCoherent f :=
  sorry

/-- Lemma 76.48.3 (3): Let `S` be a scheme. Let `f : X ⟶ Y` be a local complete
intersection morphism of algebraic spaces over `S`. Then `f` is perfect. -/
@[stacks 06C6]
instance IsLocalCompleteIntersection.perfect {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsLocalCompleteIntersection f] :
    Perfect f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
