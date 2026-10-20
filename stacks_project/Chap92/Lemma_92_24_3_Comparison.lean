/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.CotangentComplex.OverRing
public import ReasLib.AlgebraicGeometry.Scheme.OverSpec
public import stacks_project.Chap92.Definition_92_24_1_Morphism
public import stacks_project.Chap92.Lemma_92_18_8_Triangle

/-!
# Cotangent complex of a scheme over a ring

This module provides the namespaced comparison API for the cotangent complex
of a scheme over the spectrum of a ring.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry

noncomputable section

universe u

/- The canonical comparison from the cotangent complex over a constant ring sheaf
 to the cotangent complex of the scheme morphism. -/
#check (AlgebraicGeometry.Scheme.Cotangent.overRingCompare :
  ∀ (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)],
    AlgebraicGeometry.Scheme.Cotangent.constCotangent Λ X ⟶
      DerivedCategory.Q.obj (AlgebraicGeometry.Scheme.Hom.cotangentComplex
        (X ↘ AlgebraicGeometry.Spec Λ)))
