/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement
public import ReasLib.CategoryTheory.Filtration.Strict
public import ReasLib.CategoryTheory.Filtration.ZeroMorphisms
public import ReasLib.CategoryTheory.GradedObject.Preadditive
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Strict Bounded-Below Filtered Replacements

This module provides the property-neutral comparison datum used for filtered resolutions.  The
ambient category of complexes is supplied with both a functor to filtered objects, which records
termwise strictness, and a functor to graded objects, which records the chosen notion of filtered
quasi-isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe w v u

namespace CochainComplex

namespace FilteredReplacement

variable {A : Type u} [Category.{v} A] [Abelian A] [CategoryWithHomology (GradedObject ℤ A)]
variable {B : Type w} [Category.{v} B] [HasZeroMorphisms B]

/-- A bounded-below, termwise-monomorphic replacement whose components are strict after applying
`filtered`, and which is a quasi-isomorphism after applying the chosen `graded` functor. -/
@[stacks 05TW "strict graded replacement datum"]
structure IsStrict
    (filtered : B ⥤ FilteredObject A) (graded : B ⥤ GradedObject ℤ A)
    [graded.PreservesZeroMorphisms]
    (P : ObjectProperty B) (a : ℤ) {K : CochainComplex B ℤ}
    (I : Plus.TermsIn P) (α : K ⟶ I) : Prop extends
    Plus.TermsIn.Bounded.Mono P a K I α where
  /-- The comparison is a quasi-isomorphism after applying the chosen graded functor. -/
  quasiIso : QuasiIso ((graded.mapHomologicalComplex (ComplexShape.up ℤ)).map α)
  /-- Every component becomes a strict filtered morphism. -/
  term_strict (n : ℤ) : FilteredObject.Hom.Strict (filtered.map (α.f n))

end FilteredReplacement

end CochainComplex
