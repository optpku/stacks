/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.Renumber.FromZero
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Renumber.Preadditive
public import ReasLib.CategoryTheory.Homology.SpectralSequence.PositivePage.Preadditive
import Mathlib.Tactic.CrossRefAttribute

/-!
# Additivity of standard renumbering from page zero
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.CohomologicalSpectralSequence.Renumber.FromZero

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Forgetting the zeroth page and applying the standard renumbering is additive. -/
@[stacks 0G1Y "additivity of spectral-sequence renumbering from page zero", stacks 0G20]
noncomputable instance functor_additive :
    (functor (C := C)).Additive := sorry

end CategoryTheory.CohomologicalSpectralSequence.Renumber.FromZero
