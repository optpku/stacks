/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.GradedPieceColumn.Map
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Functorial homology of graded-piece columns

The objectwise homology comparison for a reindexed graded-piece column is natural in the
filtered complex.  This leaf packages those comparisons as a natural isomorphism, so later page
constructions can use functor composition instead of rebuilding componentwise naturality.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.GradedPiece.Column

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCokernels C]
variable [CategoryWithHomology C]

/-- Homology of a fixed reindexed graded-piece column is naturally the corresponding graded-piece
homology in total degree `p + q`. -/
@[stacks 012M "functorial homology comparison for a graded-piece column"]
noncomputable def homologyNatIso (p q : ℤ) :
    functor (C := C) p ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q ≅
      FilteredComplex.gradedPieceFunctor p ⋙
        HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (p + q) :=
  NatIso.ofComponents (fun K ↦ (homologyIso K p q))
    (fun f ↦ homologyIso_hom_naturality f p q)

/-- The forward component of the graded-piece-column homology natural isomorphism is the
objectwise column comparison. -/
@[simp, stacks 012M "forward component of graded-piece-column homology"]
theorem homologyNatIso_hom_app (p q : ℤ) (K : FilteredComplex C) :
    (homologyNatIso (C := C) p q).hom.app K = (homologyIso K p q).hom := sorry

/-- The inverse component of the graded-piece-column homology natural isomorphism is the
objectwise inverse comparison. -/
@[simp, stacks 012M "inverse component of graded-piece-column homology"]
theorem homologyNatIso_inv_app (p q : ℤ) (K : FilteredComplex C) :
    (homologyNatIso (C := C) p q).inv.app K = (homologyIso K p q).inv := sorry

end CategoryTheory.FilteredComplex.GradedPiece.Column
