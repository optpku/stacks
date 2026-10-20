/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.GradedPieceColumn
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additivity of graded-piece columns

The fixed-column construction is a functor on filtered complexes.  This leaf registers its
additive structure independently of the column computation and homology comparison APIs.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCokernels C]

namespace GradedPiece.Column

/-- A fixed graded-piece column is additive in the filtered-complex morphism. -/
@[stacks 012M "additivity of the graded-piece column functor"]
noncomputable instance functor_additive (p : ℤ) :
    (functor (C := C) p).Additive := sorry

#synth (functor (C := C) 0).Additive

end GradedPiece.Column

end CategoryTheory.FilteredComplex
