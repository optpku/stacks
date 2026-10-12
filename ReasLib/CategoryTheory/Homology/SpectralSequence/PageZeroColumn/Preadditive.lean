/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageZeroColumn
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Preadditive
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additivity of fixed zeroth-page columns

The fixed-column restriction is additive once the coefficient category is abelian.  This leaf
keeps that reusable instance separate from the column construction and its homology comparisons.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.CohomologicalSpectralSequence.PageZeroColumn

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A fixed zeroth-page column is an additive functor of spectral sequences. -/
@[stacks 012M "additivity of a fixed zeroth-page column"]
noncomputable instance functor_additive (p : ℤ) :
    (functor (C := C) p).Additive := sorry

#synth (functor (C := C) 0).Additive

end CategoryTheory.CohomologicalSpectralSequence.PageZeroColumn
