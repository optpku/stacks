/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of separation axioms for morphisms of algebraic spaces

Separated, locally separated, and quasi-separated morphisms of algebraic
spaces are stable under composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.4.8 (1): Separated morphisms of algebraic spaces are stable under
composition. -/
@[stacks 03KQ]
instance separated_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Separated S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of separated morphisms of algebraic spaces is separated. -/
instance separated_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Separated f] [Separated g] :
    Separated (f ≫ g) := sorry

/-- Lemma 67.4.8 (2): Locally separated morphisms of algebraic spaces are stable
under composition. -/
@[stacks 03KQ]
instance locallySeparated_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@LocallySeparated S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of locally separated morphisms of algebraic spaces is locally
separated. -/
instance locallySeparated_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallySeparated f] [LocallySeparated g] :
    LocallySeparated (f ≫ g) := sorry

/-- Lemma 67.4.8 (3): Quasi-separated morphisms of algebraic spaces are stable
under composition. -/
@[stacks 03KQ]
instance quasiSeparated_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@QuasiSeparated S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of quasi-separated morphisms of algebraic spaces is
quasi-separated. -/
instance quasiSeparated_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiSeparated f] [QuasiSeparated g] :
    QuasiSeparated (f ≫ g) := sorry

end AlgebraicGeometry.AlgebraicSpace
