/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageOneRow
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Preadditive
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additivity of fixed first-page rows

The fixed-row restriction is additive once the coefficient category is abelian.  This leaf keeps
the support instance independent of the row computation and page-two comparison declarations.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.CohomologicalSpectralSequence.PageOneRow

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A fixed first-page row is an additive functor of spectral sequences. -/
@[stacks 0130 "additivity of a fixed first-page row"]
noncomputable instance functor_additive (q : ℤ) :
    (functor (C := C) q).Additive := sorry

end CategoryTheory.CohomologicalSpectralSequence.PageOneRow
