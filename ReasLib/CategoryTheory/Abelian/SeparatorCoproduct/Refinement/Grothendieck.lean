/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

/-- Lemma 19.12.1: in a Grothendieck abelian category, an epimorphism `π : M ⟶ N` and a
separator `U` admit a subobject of `M` which still surjects onto `N` and whose size is at most the
source bound `c(|N|)`. -/
@[stacks 079J "Grothendieck specialization"]
theorem exists_refinement
    (hU : IsSeparator U) (π : M ⟶ N) [Epi π] :
    ∃ P : Subobject M,
      Epi (P.arrow ≫ π) ∧
        Cardinal.mk (Subobject (P : C)) ≤
          Subobject.coproductCardinal U (Subobject.smallCardinal N) := sorry

end Grothendieck

end CategoryTheory.SeparatorEpi
