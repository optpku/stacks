/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.GenericPoint
public import stacks_project.Chap65.Example_65_14_8_Action
public import stacks_project.Chap65.Lemma_65_14_6_Equivariant

/-!
# Source compatibility for the generic point of the affine-line quotient

The generic-point constructions are reusable declarations owned by the corresponding library
module. This file retains the source-facing import and a typed compatibility check.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation

universe u

#check (genericHom : ∀ (k : Type u) [Field k] [CharZero k],
  AlgebraicGeometry.Scheme.PreRelation.specToQuotientHom
    (action k) (genericStructure k))
