/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import stacks_project.Chap62.Lemma_62_6_5
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 62.6.14

Pushforward of relative cycles along a thickening of schemes locally of finite
type over a locally Noetherian base.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- The closed-immersion pushforward of an element of `z(X/S, r)` lies in
`z(X'/S, r)`. -/
theorem groupPushforward_mem {X X' S : Scheme.{u}} (fX : X ⟶ S) (fX' : X' ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType fX] [LocallyOfFiniteType fX']
    (i : X ⟶ X') [IsClosedImmersion i] (hc : i ≫ fX' = fX) (r : ℕ)
    (α : group fX r) :
    pushforward fX' i hc (α : Family fX r) ∈ group fX' r := sorry

/-- Pushforward of relative `r`-cycles along a closed immersion over `S`. -/
noncomputable def groupPushforward {X X' S : Scheme.{u}} (fX : X ⟶ S)
    (fX' : X' ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType fX]
    [LocallyOfFiniteType fX'] (i : X ⟶ X') [IsClosedImmersion i]
    (hc : i ≫ fX' = fX) (r : ℕ) : group fX r →+ group fX' r where
  toFun α :=
    ⟨pushforward fX' i hc (α : Family fX r),
      groupPushforward_mem fX fX' i hc r α⟩
  map_zero' := sorry
  map_add' := sorry

/-- The underlying fibrewise family of `groupPushforward` is family-level
pushforward. -/
theorem groupPushforward_apply {X X' S : Scheme.{u}} (fX : X ⟶ S)
    (fX' : X' ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType fX]
    [LocallyOfFiniteType fX'] (i : X ⟶ X') [IsClosedImmersion i]
    (hc : i ≫ fX' = fX) (r : ℕ) (α : group fX r) :
    (groupPushforward fX fX' i hc r α : Family fX' r) =
      pushforward fX' i hc (α : Family fX r) := sorry

/-- Pushforward of families of `r`-cycles on fibres along a thickening over `S`
is a bijection. -/
theorem pushforward_bijective {X X' S : Scheme.{u}} (fX : X ⟶ S) (fX' : X' ⟶ S)
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fX'] (i : X ⟶ X')
    [IsThickening i] (hc : i ≫ fX' = fX) (r : ℕ) :
    Function.Bijective (fun α : Family fX r ↦ pushforward fX' i hc α) := sorry

/-- Lemma 62.6.14: if `S` is locally Noetherian and `i : X ⟶ X'` is a thickening
of schemes locally of finite type over `S`, then for every `r ≥ 0` the
pushforward `i_* : z(X/S, r) → z(X'/S, r)` is a bijection. -/
@[stacks 0H5E]
theorem groupPushforward_bijective {X X' S : Scheme.{u}} (fX : X ⟶ S)
    (fX' : X' ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType fX]
    [LocallyOfFiniteType fX'] (i : X ⟶ X') [IsThickening i]
    (hc : i ≫ fX' = fX) (r : ℕ) :
    Function.Bijective (groupPushforward fX fX' i hc r) := sorry

end AlgebraicGeometry.RelativeCycle
