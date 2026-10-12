/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap62.Definition_62_6_1_Specialization
public import stacks_project.Chap62.Lemma_62_6_6_Relative
public import stacks_project.Chap62.Lemma_62_8_2_Operations

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Lemma 62.6.5: if `S` is locally Noetherian and `i : X ⟶ Y` is a closed
immersion of schemes locally of finite type over `S`, then a family `α` of
`r`-cycles on fibres of `X / S` is a relative `r`-cycle if and only if the
pushforward `i_*α` is a relative `r`-cycle on `Y / S`. -/
@[stacks 0H54]
theorem isRelative_iff_pushforward {X Y S : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType fX] [LocallyOfFiniteType fY]
    (i : X ⟶ Y) [IsClosedImmersion i] (hc : i ≫ fY = fX) (r : ℕ) (α : Family fX r) :
    IsRelative α ↔ IsRelative (pushforward fY i hc α) := sorry

/-- Closed-immersion pushforward of a relative `r`-cycle remains a relative
`r`-cycle. -/
theorem isRelative_pushforward {X Y S : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType fX] [LocallyOfFiniteType fY]
    (i : X ⟶ Y) [IsClosedImmersion i] (hc : i ≫ fY = fX) (r : ℕ) (α : Family fX r) :
    IsRelative α → IsRelative (pushforward fY i hc α) := sorry

/-- If the closed-immersion pushforward of a fibrewise family is a relative
`r`-cycle, then the original family is a relative `r`-cycle. -/
theorem isRelative_of_isRelative_pushforward {X Y S : Scheme.{u}} (fX : X ⟶ S)
    (fY : Y ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType fX]
    [LocallyOfFiniteType fY] (i : X ⟶ Y) [IsClosedImmersion i]
    (hc : i ≫ fY = fX) (r : ℕ) (α : Family fX r) :
    IsRelative (pushforward fY i hc α) → IsRelative α := sorry

/-- A fibrewise family lies in `z(X/S, r)` if and only if its closed-immersion
pushforward lies in `z(Y/S, r)`. -/
theorem mem_group_iff_pushforward {X Y S : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType fX] [LocallyOfFiniteType fY]
    (i : X ⟶ Y) [IsClosedImmersion i] (hc : i ≫ fY = fX) (r : ℕ) (α : Family fX r) :
    α ∈ group fX r ↔ pushforward fY i hc α ∈ group fY r := sorry

end AlgebraicGeometry.RelativeCycle
