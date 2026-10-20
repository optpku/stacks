/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite.Composition
import StacksCheckRecall

/-!
# Composition of quasi-finite morphisms of algebraic spaces

The composition of a pair of quasi-finite morphisms of algebraic spaces is
quasi-finite, and the same holds for morphisms that are locally quasi-finite
in the Stacks sense (locally of finite type and locally quasi-finite).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.27.3 (1): The composition of quasi-finite morphisms of algebraic
spaces is quasi-finite. -/
@[stacks 03XK] #check (AlgebraicGeometry.AlgebraicSpace.quasiFinite_comp :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z),
    [QuasiFinite f] → [QuasiFinite g] → QuasiFinite (f ≫ g))

/- Lemma 67.27.3 (2): The composition of locally quasi-finite morphisms of
algebraic spaces is locally quasi-finite. -/
@[stacks 03XK] #check (AlgebraicGeometry.AlgebraicSpace.locallyQuasiFinite_comp :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z),
    [LocallyOfFiniteType f] → [LocallyQuasiFinite f] →
    [LocallyOfFiniteType g] → [LocallyQuasiFinite g] →
      LocallyOfFiniteType (f ≫ g) ∧ LocallyQuasiFinite (f ≫ g))

#check (AlgebraicGeometry.AlgebraicSpace.quasiFinite_isStableUnderComposition :
  ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderComposition
    (@QuasiFinite S : MorphismProperty (AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.locallyQuasiFinite_isStableUnderComposition :
  ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderComposition
    (@LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S :
      MorphismProperty (AlgebraicSpace S)))

end AlgebraicGeometry.AlgebraicSpace
