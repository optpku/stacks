/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.ClosedSubscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Associated closed-subscheme cycle families under composition

Composition of associated fibre-cycle families of closed subschemes recovers the
associated family of the scheme-theoretic fibre product when the first closed
subscheme is flat over the intermediate scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace CyclesOnFibers

/-- The fibrewise dimension of `Z ⊔ W.comap f`, which realizes the
scheme-theoretic fibre product `Z ×_Y W ⊂ X`, is at most `r + e` when `Z` and
`W` have fibrewise relative dimension at most `r` and `e` and `Z` is flat
over `Y`. -/
theorem fiberClosedSubschemeDimensionLE_sup_comap {S X Y : Scheme.{u}}
    (p : Y ⟶ S) (f : X ⟶ Y) [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    (Z : X.IdealSheafData) (r : ℕ) (hZ : f.fiberClosedSubschemeDimensionLE Z r)
    (W : Y.IdealSheafData) (e : ℕ) (hW : p.fiberClosedSubschemeDimensionLE W e)
    [Flat (Z.subschemeι ≫ f)] :
    (f ≫ p).fiberClosedSubschemeDimensionLE (Z ⊔ W.comap f) (r + e) := sorry

/-- Let `f : X ⟶ Y` and `Y ⟶ S` be morphisms of schemes, both
locally of finite type. Let `r, e ≥ 0`. Let `Z ⊂ X` be a closed subscheme of
relative dimension `≤ r` over `Y`. Let `W ⊂ Y` be a closed subscheme of
relative dimension `≤ e` over `S`. If `α = [Z/X/Y]_r` as
`closedSubschemeFiberCycleFamily f Z r hZ` and `β = [W/Y/S]_e` as
`closedSubschemeFiberCycleFamily p W e hW`, and `Z` is flat over `Y`, then
`α ∘ β = [Z ×_Y W / X/S]_{r + e}`, where `Z ×_Y W ⊂ X` is the closed
subscheme `Z ⊔ W.comap f`. -/
theorem comp_closedSubschemeFiberCycleFamily {S X Y : Scheme.{u}}
    (p : Y ⟶ S) (f : X ⟶ Y) [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    (Z : X.IdealSheafData) (r : ℕ) (hZ : f.fiberClosedSubschemeDimensionLE Z r)
    (W : Y.IdealSheafData) (e : ℕ) (hW : p.fiberClosedSubschemeDimensionLE W e)
    [Flat (Z.subschemeι ≫ f)] :
    comp (closedSubschemeFiberCycleFamily f Z r hZ)
        (closedSubschemeFiberCycleFamily p W e hW) =
      FiberCycleFamily.reindex (Int.natCast_add r e)
        (closedSubschemeFiberCycleFamily (f ≫ p) (Z ⊔ W.comap f) (r + e)
          (fiberClosedSubschemeDimensionLE_sup_comap p f Z r hZ W e hW)) := sorry

/-- At each point of each fibre of `X / S`, the coefficient of the composite
of the associated cycle families of `Z ⊂ X` and `W ⊂ Y` equals the coefficient
of the associated cycle family of `Z ×_Y W ⊂ X` in degree `r + e`, when `Z`
is flat over `Y` and the fibre dimensions of `Z` and `W` are bounded by `r`
and `e`. -/
theorem comp_closedSubschemeFiberCycleFamily_apply {S X Y : Scheme.{u}}
    (p : Y ⟶ S) (f : X ⟶ Y) [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    (Z : X.IdealSheafData) (r : ℕ) (hZ : f.fiberClosedSubschemeDimensionLE Z r)
    (W : Y.IdealSheafData) (e : ℕ) (hW : p.fiberClosedSubschemeDimensionLE W e)
    [Flat (Z.subschemeι ≫ f)] (s : S) (x : (f ≫ p).fiber s) :
    toAlgebraicCycle
        (comp (closedSubschemeFiberCycleFamily f Z r hZ)
          (closedSubschemeFiberCycleFamily p W e hW)) s x =
      toAlgebraicCycle
        (FiberCycleFamily.reindex (Int.natCast_add r e)
          (closedSubschemeFiberCycleFamily (f ≫ p) (Z ⊔ W.comap f) (r + e)
            (fiberClosedSubschemeDimensionLE_sup_comap p f Z r hZ W e hW)))
        s x := sorry

end CyclesOnFibers
end AlgebraicGeometry.Scheme.Hom
