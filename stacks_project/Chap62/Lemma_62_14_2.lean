module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Operations
public import stacks_project.Chap62.Lemma_62_13_5
public import stacks_project.Chap62.Lemma_62_14_2_Self
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of identity associated cycle families

This file records the identity-closed-subscheme special case of
`comp_closedSubschemeFiberCycleFamily`: the associated families of `X ⊂ X`
and `Y ⊂ Y` compose to the associated family of `X ⊂ X` over `S`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace CyclesOnFibers

/-- Lemma 62.14.2: Let `f : X ⟶ Y` and `p : Y ⟶ S` be morphisms of schemes.
Assume `S` is locally Noetherian, `p` is locally of finite type and flat of
relative dimension `e ≥ 0`, and `f` is locally of finite type and flat of
relative dimension `r ≥ 0`. Then `[X/X/Y]_r ∘ [Y/Y/S]_e = [X/X/S]_{r+e}`
in `z(X/S, r+e)`. -/
@[stacks 0H6S]
theorem comp_closedSubschemeFiberCycleFamily_bot {S X Y : Scheme.{u}}
    (p : Y ⟶ S) (f : X ⟶ Y) (e r : ℕ) [IsLocallyNoetherian S]
    [Flat p] [RelativeDimension p e] [Flat f] [RelativeDimension f r] :
    comp (closedSubschemeFiberCycleFamily f (⊥ : X.IdealSheafData) r
          (fiberClosedSubschemeDimensionLE_bot f r))
        (closedSubschemeFiberCycleFamily p (⊥ : Y.IdealSheafData) e
          (fiberClosedSubschemeDimensionLE_bot p e)) =
      FiberCycleFamily.reindex (Int.natCast_add r e)
        (closedSubschemeFiberCycleFamily (f ≫ p) (⊥ : X.IdealSheafData) (r + e)
          (fiberClosedSubschemeDimensionLE_bot (f ≫ p) (r + e))) := sorry

/-- Evaluating `comp_closedSubschemeFiberCycleFamily_bot` compares coefficients
of both sides at a point of the fibre of `X / S`. -/
theorem comp_closedSubschemeFiberCycleFamily_bot_apply {S X Y : Scheme.{u}}
    (p : Y ⟶ S) (f : X ⟶ Y) (e r : ℕ) [IsLocallyNoetherian S]
    [Flat p] [RelativeDimension p e] [Flat f] [RelativeDimension f r]
    (s : S) (x : (f ≫ p).fiber s) :
    toAlgebraicCycle
        (comp (closedSubschemeFiberCycleFamily f (⊥ : X.IdealSheafData) r
            (fiberClosedSubschemeDimensionLE_bot f r))
          (closedSubschemeFiberCycleFamily p (⊥ : Y.IdealSheafData) e
            (fiberClosedSubschemeDimensionLE_bot p e)))
        s x =
      toAlgebraicCycle
        (FiberCycleFamily.reindex (Int.natCast_add r e)
          (closedSubschemeFiberCycleFamily (f ≫ p) (⊥ : X.IdealSheafData) (r + e)
            (fiberClosedSubschemeDimensionLE_bot (f ≫ p) (r + e))))
        s x := sorry

/-- After reindexing, the associated identity family of `f ≫ p` lies in
`z(X/S, r+e)`. -/
theorem comp_closedSubschemeFiberCycleFamily_bot_mem_group {S X Y : Scheme.{u}}
    (p : Y ⟶ S) (f : X ⟶ Y) (e r : ℕ) [IsLocallyNoetherian S]
    [Flat p] [RelativeDimension p e] [Flat f] [RelativeDimension f r] :
    FiberCycleFamily.reindex (Int.natCast_add r e)
        (closedSubschemeFiberCycleFamily (f ≫ p) (⊥ : X.IdealSheafData) (r + e)
          (fiberClosedSubschemeDimensionLE_bot (f ≫ p) (r + e))) ∈
      RelativeCycle.group (f ≫ p) (r + e) := sorry

end CyclesOnFibers
end AlgebraicGeometry.Scheme.Hom
