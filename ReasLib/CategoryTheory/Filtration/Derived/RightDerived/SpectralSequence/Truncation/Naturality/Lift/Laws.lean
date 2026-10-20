/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Preimage.Lift.Laws
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Naturality.Lift.Operations
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Compatibility names for laws of truncation-filtration lifts

The laws are owned by `DerivedCategory.Preimage.Lift`; this file exports their historical
truncation-spectral-sequence names.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe wA vA uA

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]

namespace Realization.Lift

export _root_.CategoryTheory.DerivedCategory.Preimage.Lift
  (reindex_rfl reindex_trans reindex_symm id_comp comp_id assoc)

end Realization.Lift

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation
