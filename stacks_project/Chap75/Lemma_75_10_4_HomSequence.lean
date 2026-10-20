/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.ComposableArrows.Three
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import ReasLib.Algebra.Homology.DerivedCategory.Adjunction
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Adjunction
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Equiv
public import stacks_project.Chap75.Lemma_75_10_1_Sequence

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.MayerVietoris.Hom

/-! # Derived étale adjunction and restriction composition

The public imports retain the derived module and gluing APIs used by the
source-facing consumers. The checks identify the shared adjunction and
composition comparison.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.lowerShriekDerivedAdjunction :
  ∀ {S : Scheme.{u}} {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f],
    lowerShriekDerived f ⊣ restrictFunctorDerived f)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.restrictFunctorDerivedCompIso :
  ∀ {S : Scheme.{u}} {U X : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
    {W : AlgebraicSpace S} (p : W ⟶ U) [Etale p],
    restrictFunctorDerived j ⋙ restrictFunctorDerived p ≅
      restrictFunctorDerived (p ≫ j))
