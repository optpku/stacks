/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap74.Definition_74_20_1_SmoothLocal
public import stacks_project.Chap74.Lemma_74_10_2_BaseChange

/-!
# Smooth locality implications

A morphism property of algebraic spaces that is smooth local on source-and-target
is local for the smooth precoverage on the source and on the target, and is
stable under postcomposition with smooth morphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsSmoothLocalAtSourceAndTarget

variable {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}

/-- A morphism property that is smooth local on source-and-target is local for
smooth covers of the source. -/
instance toIsLocalAtSource [IsSmoothLocalAtSourceAndTarget P] :
    P.IsLocalAtSource (smoothPrecoverage S) :=
  sorry

/-- A morphism property that is smooth local on source-and-target is local for
smooth covers of the target. -/
instance toIsLocalAtTarget [IsSmoothLocalAtSourceAndTarget P] :
    P.IsLocalAtTarget (smoothPrecoverage S) :=
  sorry

/-- A morphism property that is smooth local on source-and-target is preserved by
postcomposition with a smooth morphism. -/
instance toRespectsRightSmooth [IsSmoothLocalAtSourceAndTarget P] :
    P.RespectsRight (@Smooth S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

/-- If `f` has a smooth-local-on-source-and-target property and `g` is smooth,
then `f ≫ g` has the property. -/
theorem postcomp [IsSmoothLocalAtSourceAndTarget P] {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : P f) (hg : Smooth g) : P (f ≫ g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsSmoothLocalAtSourceAndTarget
