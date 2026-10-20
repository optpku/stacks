/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Support
public import Mathlib.Data.Int.Interval
public import ReasLib.CategoryTheory.Filtration.Functors
public import ReasLib.CategoryTheory.Filtration.FiniteProjective
public import ReasLib.LinearAlgebra.Trace.CommutatorQuotient.FiniteProjective
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits FilteredObject ModuleCat Ring
open FilteredObject.Finite
open scoped FilteredObject.Finite Ring ZeroObject

noncomputable section

universe u v

namespace CategoryTheory.FilteredObject.Finite

variable {Λ : Type u} [Ring Λ]
variable (P : Filᶠ(ModuleCat.{v} Λ)) [IsFilteredFiniteProjective P.obj]

/-- Let `P` be a filtered finite projective object of
`Filᶠ(ModuleCat Λ)`, and let `f : P ⟶ P` be an endomorphism in
`Filᶠ(ModuleCat Λ)`. Then `Tr(f|_P)`, the finite-projective trace
`LinearMap.FiniteProjective.traceNatural` of
`(Forget.functor (ModuleCat Λ)).map f` in `Λ♮`, equals
`∑ᶠ p, Tr(f|_{gr^p P})`, the finsum of the traces of the induced maps
`f.hom.gradedPieceMap p` on associated graded pieces. -/
@[stacks 03TL]
theorem traceNatural_eq_sum_gradedPiece (f : P ⟶ P) :
    LinearMap.FiniteProjective.traceNatural
        (ModuleCat.Hom.hom ((Forget.functor (ModuleCat.{v} Λ)).map f)) =
      ∑ᶠ p : ℤ, LinearMap.FiniteProjective.traceNatural
        (ModuleCat.Hom.hom (f.hom.gradedPieceMap p)) :=
  sorry

/-- The additivity of the finite-projective trace along a finite filtration may be
written as a finite sum over any window `Finset.Ico a b` with `F^a P = ⊤` and
`F^b P = ⊥`. -/
theorem traceNatural_eq_sum_gradedPiece_Ico (f : P ⟶ P) {a b : ℤ}
    (ha : IndexedFiltration.stage P.obj.filtration a = ⊤)
    (hb : IndexedFiltration.stage P.obj.filtration b = ⊥) :
    LinearMap.FiniteProjective.traceNatural
        (ModuleCat.Hom.hom ((Forget.functor (ModuleCat.{v} Λ)).map f)) =
      ∑ p ∈ Finset.Ico a b,
        LinearMap.FiniteProjective.traceNatural
          (ModuleCat.Hom.hom (f.hom.gradedPieceMap p)) :=
  sorry

/-- Only finitely many graded-piece traces of a finite-filtered endomorphism are
nonzero. -/
theorem traceNatural_gradedPiece_finiteSupport (f : P ⟶ P) :
    (Function.support fun p : ℤ ↦
        LinearMap.FiniteProjective.traceNatural
          (ModuleCat.Hom.hom (f.hom.gradedPieceMap p))).Finite :=
  sorry

end CategoryTheory.FilteredObject.Finite
