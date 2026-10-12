/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Definition_76_46_1_PseudoCoherent
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation

/-!
# Pseudo-coherent morphisms of algebraic spaces are locally of finite presentation
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.46.4: A pseudo-coherent morphism is locally of finite presentation. -/
@[stacks 06BU]
instance locallyOfFinitePresentation_of_pseudoCoherent {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [PseudoCoherent f] :
    LocallyOfFinitePresentation f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
