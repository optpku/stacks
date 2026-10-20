/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Model.Comparison
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequenceComparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Unbounded filtered right-derived realizations

A realization retains an explicit filtered K-injective resolution, its cohomology comparison, and concrete spectral-sequence association data.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open Functor.RightDerived.Homotopy

noncomputable section

universe w wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F]

namespace SpectralSequence

/-- A realization of the unbounded right-derived spectral sequence of a filtered complex.  The
associated spectral sequence and every cohomology comparison are tied to the explicit resolution. -/
@[stacks 0BKK "unbounded filtered right-derived spectral-sequence realization"]
structure Realization (K : FilteredComplex A) where
  /-- The explicit filtered K-injective resolution used by the realization. -/
  resolution : KInjectiveResolution K
  /-- Comparison of the filtered model with total right-derived cohomology. -/
  comparison : Model.Comparison F resolution
  /-- A spectral sequence with concrete association data for the filtered model. -/
  associated : AssociatedSpectralSequence (model F resolution)

end SpectralSequence

end CategoryTheory.FilteredComplex.RightDerived

