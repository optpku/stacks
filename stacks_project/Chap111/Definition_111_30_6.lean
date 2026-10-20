/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.QuasiIso
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]

/- Definition 111.30.6: for an abelian category `𝒜`, a morphism `α : K ⟶ L` of cochain complexes
of `Fil(𝒜)` (`FilteredComplex 𝒜`) is a filtered quasi-isomorphism when for each `p : ℤ` the
induced map `gr^p(K) ⟶ gr^p(L)` (`FilteredComplex.gradedPieceMap α p`) is a quasi-isomorphism. -/
@[stacks 028D] #check (CategoryTheory.FilteredComplex.IsFilteredQuasiIso :
  ∀ {K L : FilteredComplex A}, (K ⟶ L) → Prop)
