/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap62.Definition_62_8_1_Effective
public import stacks_project.Chap62.Lemma_62_6_11_RelativeCycle

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Lemma 62.8.6: if `S` is locally Noetherian, `f : X ⟶ S` is locally of
finite type, and `α` is an effective relative `r`-cycle on `X / S`, then
`Supp(α)` is closed in `X`. Here `Supp(α)` is `RelativeCycle.support α`. -/
@[stacks 0H5W]
theorem isClosed_support_of_isEffective {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ} {α : Family f r}
    (hα : IsRelative α) (h_eff : IsEffective α) :
    IsClosed (support α) := sorry

/-- The support of a family in `z^{eff}(X/S, r)` is closed in `X`. -/
theorem isClosed_support_of_mem_effective {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ} {α : Family f r}
    (hα : α ∈ effective f r) :
    IsClosed (support α) := sorry

end AlgebraicGeometry.RelativeCycle
