/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap62.Lemma_62_8_2_Effective
public import stacks_project.Chap62.Definition_62_6_1_Specialization

/-!
# Effective relative cycles

This file names the additive monoid `z^{eff}(X/S, r)` of effective relative
`r`-cycles on a locally finite type morphism `f : X ⟶ S` from a locally
Noetherian scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

#check (AlgebraicGeometry.RelativeCycle.effective :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] (r : ℕ), AddSubmonoid (Family f r))

#check (AlgebraicGeometry.RelativeCycle.mem_effective :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] (r : ℕ) (α : Family f r),
    α ∈ effective f r ↔ IsRelative α ∧ IsEffective α)

#check (AlgebraicGeometry.RelativeCycle.mem_effective_iff_nonneg :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] (r : ℕ) (α : Family f r),
    α ∈ effective f r ↔
      IsRelative α ∧
        ∀ s : S, ∀ x : f.fiber s,
          0 ≤ CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r (α s) x)

end AlgebraicGeometry.RelativeCycle
