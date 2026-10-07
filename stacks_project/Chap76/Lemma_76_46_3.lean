module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import stacks_project.Chap76.Definition_76_46_1_PseudoCoherent

/-!
# Composition of pseudo-coherent morphisms of algebraic spaces

A composition of pseudo-coherent morphisms of algebraic spaces is
pseudo-coherent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.46.3: A composition of pseudo-coherent morphisms is
pseudo-coherent. -/
@[stacks 06BT]
instance PseudoCoherent.comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [PseudoCoherent f] [PseudoCoherent g] :
    PseudoCoherent (f ≫ g) :=
  sorry

/-- Pseudo-coherent morphisms of algebraic spaces are stable under
composition. -/
instance PseudoCoherent.instIsStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@PseudoCoherent S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
