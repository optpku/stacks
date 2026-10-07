module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import stacks_project.Chap62.Example_62_5_4_AssociatedCycle
public import stacks_project.Chap62.Lemma_62_6_8

/-!
# Identity closed-subscheme fibre-cycle families

This file records that the identity closed subscheme `⊥ ⊂ X` has fibrewise
dimension at most `r` when `X ⟶ S` has relative dimension `r`, and that the
associated family `[X/X/S]_r` is a relative cycle.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The identity closed subscheme `⊥ ⊂ X` has fibrewise dimension at most `r`
when `f : X ⟶ S` has relative dimension `r`. -/
theorem fiberClosedSubschemeDimensionLE_bot {X S : Scheme.{u}} (f : X ⟶ S)
    (r : ℕ) [RelativeDimension f r] :
    f.fiberClosedSubschemeDimensionLE (⊥ : X.IdealSheafData) r := sorry

/-- The associated fibre-cycle family of the identity closed subscheme is a
relative `r`-cycle when `f` is flat of relative dimension `r` and `S` is
locally Noetherian. -/
theorem closedSubschemeFiberCycleFamily_bot_isRelative {X S : Scheme.{u}}
    (f : X ⟶ S) [IsLocallyNoetherian S] (r : ℕ) [Flat f] [RelativeDimension f r] :
    RelativeCycle.IsRelative
      (closedSubschemeFiberCycleFamily f (⊥ : X.IdealSheafData) r
        (fiberClosedSubschemeDimensionLE_bot f r)) := sorry

/-- The associated fibre-cycle family of the identity closed subscheme lies in
`z(X/S, r)` when `f` is flat of relative dimension `r` and `S` is locally
Noetherian. -/
theorem closedSubschemeFiberCycleFamily_bot_mem_group {X S : Scheme.{u}}
    (f : X ⟶ S) [IsLocallyNoetherian S] (r : ℕ) [Flat f] [RelativeDimension f r] :
    closedSubschemeFiberCycleFamily f (⊥ : X.IdealSheafData) r
        (fiberClosedSubschemeDimensionLE_bot f r) ∈
      RelativeCycle.group f r := sorry

end AlgebraicGeometry.Scheme.Hom
