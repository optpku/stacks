/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
import StacksCheckRecall

/-!
# Composition of quasi-compact morphisms of algebraic spaces

The composition of a pair of quasi-compact morphisms of algebraic spaces is
quasi-compact.
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 67.8.5: The composition of a pair of quasi-compact morphisms of algebraic spaces
is quasi-compact. -/
@[stacks 03HG] #check (AlgebraicGeometry.AlgebraicSpace.quasiCompact_isStableUnderComposition :
  ∀ {S : AlgebraicGeometry.Scheme.{u}},
    CategoryTheory.MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.AlgebraicSpace.QuasiCompact S :
        CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.quasiCompact_comp :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {X Y Z : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.AlgebraicSpace.QuasiCompact f]
    [AlgebraicGeometry.AlgebraicSpace.QuasiCompact g],
    AlgebraicGeometry.AlgebraicSpace.QuasiCompact (f ≫ g))
