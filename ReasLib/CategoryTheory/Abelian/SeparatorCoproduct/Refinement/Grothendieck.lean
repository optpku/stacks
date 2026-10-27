/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Abelian.SeparatorCoproduct.Refinement
public import ReasLib.CategoryTheory.Generator.CoproductCardinal

@[expose] public section

/-!
# Small Epi Refinements in Grothendieck Abelian Categories

This leaf specializes the small epi-refinement construction to a Grothendieck abelian category.
The ambient axioms supply exactly the small subobject lattice and coproduct used by the neutral
construction in `CategoryTheory.SeparatorEpi`.
-/

open CategoryTheory Limits

universe w v u

namespace CategoryTheory.SeparatorEpi

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
variable {U M N : C}

namespace Grothendieck

/-- In a Grothendieck abelian category, an epimorphism `π : M ⟶ N` and a
separator `U` admit a subobject of `M` which still surjects onto `N` and whose size is at most the
cardinal bound `c(|N|)`. -/
@[stacks 079J "Grothendieck specialization"]
theorem exists_refinement
    (hU : IsSeparator U) (π : M ⟶ N) [Epi π] :
    ∃ P : Subobject M,
      Epi (P.arrow ≫ π) ∧
        Cardinal.mk (Subobject (P : C)) ≤
          Subobject.coproductCardinal U (Subobject.smallCardinal N) := by
  obtain ⟨P, hp, hcard⟩ := SeparatorEpi.exists_refinement hU π
  refine ⟨P, hp, hcard.trans_eq ?_⟩
  exact Subobject.cardinalMk_coprod_const_eq_coproductCardinal U
    (Subobject.smallCardinal N) rfl

end Grothendieck

end CategoryTheory.SeparatorEpi
