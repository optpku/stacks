/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap62.Lemma_62_13_1_Comp
public import stacks_project.Chap62.Example_62_5_2_AssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Associated cycle families under composition

This file records that composition of associated fibre-cycle families of
quasi-coherent finite-type modules recovers the associated family of the
tensor with the pullback, when the first module is flat over the base.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The tensor product of quasi-coherent scheme modules is quasi-coherent. -/
instance instIsQuasicoherent_tensor {X : Scheme.{u}} {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (F ⊗ G).IsQuasicoherent := sorry

/-- The tensor product of finite-type scheme modules is of finite type. -/
instance instIsFiniteType_tensor {X : Scheme.{u}} {F G : X.Modules}
    [F.IsFiniteType] [G.IsFiniteType] :
    (F ⊗ G).IsFiniteType := sorry

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom
namespace CyclesOnFibers

/-- The fibrewise support dimension of `F ⊗ (Modules.pullback f).obj G` is at
most `r + e` when `F` and `G` have fibrewise support dimension at most `r` and
`e` and `F` is flat over `Y`. -/
theorem tensor_fiberModuleSupportDimensionLE {S X Y : Scheme.{u}}
    (p : Y ⟶ S) (f : X ⟶ Y) [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (r : ℕ)
    (hF : f.fiberModuleSupportDimensionLE F r)
    (G : Y.Modules) [G.IsQuasicoherent] [G.IsFiniteType] (e : ℕ)
    (hG : p.fiberModuleSupportDimensionLE G e)
    (hflat : Modules.flatOver F f) :
    (f ≫ p).fiberModuleSupportDimensionLE (F ⊗ (Modules.pullback f).obj G)
      (r + e) := sorry

/-- Lemma 62.13.4: Let `f : X ⟶ Y` and `Y ⟶ S` be morphisms of schemes, both
locally of finite type. Let `F` be a quasi-coherent `O_X`-module of finite
type with `dim(Supp(F_y)) ≤ r` for all `y ∈ Y`, and let `G` be a
quasi-coherent `O_Y`-module of finite type with `dim(Supp(G_s)) ≤ e` for all
`s ∈ S`. If `α = [F/X/Y]_r` as `moduleFiberCycleFamily f F r hF` and
`β = [G/Y/S]_e` as `moduleFiberCycleFamily p G e hG`, and `F` is flat over
`Y`, then `α ∘ β = [F ⊗ (Modules.pullback f).obj G / X/S]_{r + e}`. -/
@[stacks 0H6L]
theorem comp_moduleFiberCycleFamily {S X Y : Scheme.{u}}
    (p : Y ⟶ S) (f : X ⟶ Y) [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (r : ℕ)
    (hF : f.fiberModuleSupportDimensionLE F r)
    (G : Y.Modules) [G.IsQuasicoherent] [G.IsFiniteType] (e : ℕ)
    (hG : p.fiberModuleSupportDimensionLE G e)
    (hflat : Modules.flatOver F f) :
    comp (moduleFiberCycleFamily f F r hF) (moduleFiberCycleFamily p G e hG) =
      FiberCycleFamily.reindex (Int.natCast_add r e)
        (moduleFiberCycleFamily (f ≫ p) (F ⊗ (Modules.pullback f).obj G)
          (r + e)
          (tensor_fiberModuleSupportDimensionLE p f F r hF G e hG hflat)) := sorry

/-- Evaluating `comp_moduleFiberCycleFamily` compares coefficients of both
sides at a point of the fibre of `X / S`. -/
theorem comp_moduleFiberCycleFamily_apply {S X Y : Scheme.{u}}
    (p : Y ⟶ S) (f : X ⟶ Y) [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (r : ℕ)
    (hF : f.fiberModuleSupportDimensionLE F r)
    (G : Y.Modules) [G.IsQuasicoherent] [G.IsFiniteType] (e : ℕ)
    (hG : p.fiberModuleSupportDimensionLE G e)
    (hflat : Modules.flatOver F f) (s : S) (x : (f ≫ p).fiber s) :
    toAlgebraicCycle
        (comp (moduleFiberCycleFamily f F r hF)
          (moduleFiberCycleFamily p G e hG)) s x =
      toAlgebraicCycle
        (FiberCycleFamily.reindex (Int.natCast_add r e)
          (moduleFiberCycleFamily (f ≫ p) (F ⊗ (Modules.pullback f).obj G)
            (r + e)
            (tensor_fiberModuleSupportDimensionLE p f F r hF G e hG hflat)))
        s x := sorry

end CyclesOnFibers
end AlgebraicGeometry.Scheme.Hom
