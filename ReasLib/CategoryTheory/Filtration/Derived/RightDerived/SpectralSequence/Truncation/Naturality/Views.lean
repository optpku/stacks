/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation
public import ReasLib.Algebra.Homology.CochainComplex.Filtration.Truncation.Functor
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Renumber.FromZero
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Association views for truncation-filtration realizations

This file exposes the generic association used before renumbering.  The displayed sequence map
is later obtained through the neutral `CohomologicalSpectralSequence.Renumber.FromZero.map` API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

namespace Realization

/-- The association owned by the generic filtered right-derived realization. -/
@[stacks 0BKM "association of a truncation-filtration realization"]
noncomputable abbrev association {K : DerivedCategory A} (S : Realization F K) :
    FilteredComplex.Association S.filtered S.originalSequence :=
  S.original.association

end Realization

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation
