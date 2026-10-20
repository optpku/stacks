/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Composition
import StacksCheckRecall

/-!
# Composition of separation axioms for morphisms of algebraic spaces

Separated, locally separated, and quasi-separated morphisms of algebraic
spaces are stable under composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.4.8 (1): Separated morphisms of algebraic spaces are stable under
composition. -/
@[stacks 03KQ] #check
  (AlgebraicGeometry.AlgebraicSpace.separated_isStableUnderComposition :
    ∀ {S : Scheme.{u}},
    MorphismProperty.IsStableUnderComposition
      (@Separated S : MorphismProperty (AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.separated_comp :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Separated f] [Separated g],
    Separated (f ≫ g))

/- Lemma 67.4.8 (2): Locally separated morphisms of algebraic spaces are stable
under composition. -/
@[stacks 03KQ] #check
  (AlgebraicGeometry.AlgebraicSpace.locallySeparated_isStableUnderComposition :
    ∀ {S : Scheme.{u}},
    MorphismProperty.IsStableUnderComposition
      (@LocallySeparated S : MorphismProperty (AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.locallySeparated_comp :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallySeparated f] [LocallySeparated g],
    LocallySeparated (f ≫ g))

/- Lemma 67.4.8 (3): Quasi-separated morphisms of algebraic spaces are stable
under composition. -/
@[stacks 03KQ] #check
  (AlgebraicGeometry.AlgebraicSpace.quasiSeparated_isStableUnderComposition :
    ∀ {S : Scheme.{u}},
    MorphismProperty.IsStableUnderComposition
      (@QuasiSeparated S : MorphismProperty (AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.quasiSeparated_comp :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiSeparated f] [QuasiSeparated g],
    QuasiSeparated (f ≫ g))

end AlgebraicGeometry.AlgebraicSpace
