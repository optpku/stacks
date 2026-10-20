/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentComplex.OverRing
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints

/-! # Constant-coefficient cotangent complexes of algebraic spaces -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.constCotangent :
  ∀ (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)),
    DerivedCategory (Cotangent.CommModules X))

#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.spaceOverRingCompare :
  ∀ (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)),
    Cotangent.constCotangent Λ X ⟶ Cotangent.cotangent (SchemeRealization.toBase X))
