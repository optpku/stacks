/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormallySmooth

/-!
# Smooth morphisms of algebraic spaces versus formal smoothness

A morphism of algebraic spaces is smooth if and only if it is locally of finite
presentation and formally smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is smooth if and only if it is locally of
finite presentation and formally smooth. -/
theorem Smooth.iff_locallyOfFinitePresentation_and_formallySmooth
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Smooth f ↔ LocallyOfFinitePresentation f ∧ FormallySmooth f :=
  sorry

/-- A smooth morphism of algebraic spaces is formally smooth. -/
instance FormallySmooth.of_smooth {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Smooth f] : FormallySmooth f :=
  sorry

/-- A locally finitely presented, formally smooth morphism of algebraic spaces is
smooth. -/
instance Smooth.of_locallyOfFinitePresentation_of_formallySmooth
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [FormallySmooth f] : Smooth f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
