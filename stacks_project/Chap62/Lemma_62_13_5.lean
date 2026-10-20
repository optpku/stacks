/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Composition.ClosedSubscheme
import StacksCheckRecall

/-!
# Associated closed-subscheme cycle families under composition

This file records that composition of associated fibre-cycle families of closed
subschemes recovers the associated family of the scheme-theoretic fibre product,
when the first closed subscheme is flat over the base.
-/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Hom.CyclesOnFibers

universe u

/- Lemma 62.13.5: Let `f : X ⟶ Y` and `Y ⟶ S` be morphisms of schemes, both
locally of finite type. Let `r, e ≥ 0`. Let `Z ⊂ X` be a closed subscheme of
relative dimension `≤ r` over `Y`. Let `W ⊂ Y` be a closed subscheme of
relative dimension `≤ e` over `S`. If `α = [Z/X/Y]_r` as
`closedSubschemeFiberCycleFamily f Z r hZ` and `β = [W/Y/S]_e` as
`closedSubschemeFiberCycleFamily p W e hW`, and `Z` is flat over `Y`, then
`α ∘ β = [Z ×_Y W / X/S]_{r + e}`, where `Z ×_Y W ⊂ X` is the closed
subscheme `Z ⊔ W.comap f`. -/
@[stacks 0H6M] #check
  (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.comp_closedSubschemeFiberCycleFamily :
  ∀ {S X Y : Scheme.{u}}
    (p : Y ⟶ S) (f : X ⟶ Y) [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    (Z : X.IdealSheafData) (r : ℕ) (hZ : f.fiberClosedSubschemeDimensionLE Z r)
    (W : Y.IdealSheafData) (e : ℕ) (hW : p.fiberClosedSubschemeDimensionLE W e)
    [Flat (Z.subschemeι ≫ f)],
    comp (closedSubschemeFiberCycleFamily f Z r hZ)
        (closedSubschemeFiberCycleFamily p W e hW) =
      FiberCycleFamily.reindex (Int.natCast_add r e)
        (closedSubschemeFiberCycleFamily (f ≫ p) (Z ⊔ W.comap f) (r + e)
          (fiberClosedSubschemeDimensionLE_sup_comap p f Z r hZ W e hW)))
