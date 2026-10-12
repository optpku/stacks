/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap62.Lemma_62_6_6_Relative
public import stacks_project.Chap62.Lemma_62_7_3_Operations
public import stacks_project.Chap62.Lemma_62_8_2_Effective

/-!
# Zariski locality of effective fibre cycle families

This file records the fibrewise effectiveness predicate on families of
`r`-cycles on scheme-theoretic fibres, together with the source-only and
target-only Zariski locality companions for effectiveness of relative
`r`-cycles.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom.CyclesOnFibers (restrict)
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.CyclesOnFibers

/-- A family of `r`-cycles on the fibres of `f` is effective if every fibre
cycle is an effective algebraic cycle. -/
def IsEffective {X S : Scheme.{u}} {f : X ⟶ S} {r : ℤ}
    (α : CyclesOnFibers f r) : Prop :=
  ∀ s : S, α.toAlgebraicCycle s ∈ AlgebraicCycle.effective (f.fiber s)

/-- Effectiveness of a fibrewise family is equivalent to nonnegativity of every
fibre coefficient. -/
theorem isEffective_iff {X S : Scheme.{u}} {f : X ⟶ S} {r : ℤ}
    (α : CyclesOnFibers f r) :
    IsEffective α ↔
      ∀ s : S, ∀ x : f.fiber s, 0 ≤ α.toAlgebraicCycle s x := sorry

end AlgebraicGeometry.Scheme.Hom.CyclesOnFibers

namespace AlgebraicGeometry.RelativeCycle

/-- Effectiveness of a relative `r`-cycle may be checked after restriction to
the members of an open cover of the source. -/
theorem isEffective_iff_of_source_iSup_eq_top
    {X S : Scheme.{u}} [IsLocallyNoetherian S] {f : X ⟶ S} [LocallyOfFiniteType f]
    {r : ℕ} (α : Family f r) (hα : IsRelative α) {ι : Type u}
    (U : ι → X.Opens) (hU : iSup U = ⊤) :
    IsEffective α ↔
      ∀ i, IsEffective (restrict α (U i) ⊤ le_top) := sorry

/-- Effectiveness of a relative `r`-cycle may be checked after restriction to
the preimages of the members of an open cover of the target. -/
theorem isEffective_iff_of_target_iSup_eq_top
    {X S : Scheme.{u}} [IsLocallyNoetherian S] {f : X ⟶ S} [LocallyOfFiniteType f]
    {r : ℕ} (α : Family f r) (hα : IsRelative α) {κ : Type u}
    (V : κ → S.Opens) (hV : iSup V = ⊤) :
    IsEffective α ↔
      ∀ j, IsEffective (restrict α (f ⁻¹ᵁ V j) (V j) le_rfl) := sorry

end AlgebraicGeometry.RelativeCycle
