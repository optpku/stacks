/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Preimage.Lift.Operations
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Naturality.Lift.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Compatibility names for operations on truncation-filtration lifts

The operations are owned by `DerivedCategory.Preimage.Lift`; this file exports their historical
truncation-spectral-sequence names.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w wA wB vA vB uA uB uC vC

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]

namespace Realization.Lift

export _root_.CategoryTheory.DerivedCategory.Preimage.Lift
  (id comp reindex id_hom comp_hom reindex_hom ext)

end Realization.Lift

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation
