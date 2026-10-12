/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import stacks_project.Chap76.Definition_76_46_1_PseudoCoherent

/-!
# Cancellation of pseudo-coherence against pseudo-coherent postcomposition

If a composite morphism of algebraic spaces is pseudo-coherent and the second
factor is pseudo-coherent, then the first factor is pseudo-coherent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace PseudoCoherent

/-- If a composite morphism of algebraic spaces is pseudo-coherent and the
second factor is pseudo-coherent, then the first factor is pseudo-coherent. -/
theorem of_comp {S : Scheme.{u}} {X Y B : AlgebraicSpace S} (f : X ⟶ Y)
    (g : Y ⟶ B) [PseudoCoherent g] [PseudoCoherent (f ≫ g)] :
    PseudoCoherent f :=
  sorry

end PseudoCoherent

/-- Pseudo-coherent morphisms of algebraic spaces cancel against a
pseudo-coherent postcomposition. -/
instance pseudoCoherent_hasOfPostcompProperty {S : Scheme.{u}} :
    MorphismProperty.HasOfPostcompProperty
      (@PseudoCoherent S : MorphismProperty (AlgebraicSpace S))
      (@PseudoCoherent S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
