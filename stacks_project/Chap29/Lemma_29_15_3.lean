/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Operations
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- The composition of two morphisms which are locally of finite type is locally of finite type. -/
#check
  (AlgebraicGeometry.locallyOfFiniteType_comp :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      [LocallyOfFiniteType f] [LocallyOfFiniteType g], LocallyOfFiniteType (f ≫ g))

/- Lemma 29.15.3: compositions of locally finite-type morphisms are locally of finite type;
compositions of finite-type morphisms are of finite type. -/
@[stacks 01T3] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.comp :
    ∀ {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z},
      Scheme.Hom.FiniteType f → Scheme.Hom.FiniteType g → Scheme.Hom.FiniteType (f ≫ g))
