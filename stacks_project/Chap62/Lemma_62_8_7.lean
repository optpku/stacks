/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap62.Definition_62_8_1_Effective
public import stacks_project.Chap62.Definition_62_7_1_Equidimensional

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom.CyclesOnFibers (Equidimensional)

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Lemma 62.8.7: if `S` is locally Noetherian, `f : X ⟶ S` is locally of
finite type, and `α` is an effective relative `r`-cycle on `X / S`, then
`α` is equidimensional. -/
@[stacks 0H5X]
theorem equidimensional_of_isEffective {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ} {α : Family f r}
    (hα : IsRelative α) (h_eff : IsEffective α) :
    Equidimensional α := sorry

/-- A family in `z^{eff}(X/S, r)` lies in `z_equi(X/S, r)`. -/
theorem mem_equidimensional_of_mem_effective {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ} {α : Family f r}
    (hα : α ∈ effective f r) :
    α ∈ equidimensional f r := sorry

end AlgebraicGeometry.RelativeCycle
