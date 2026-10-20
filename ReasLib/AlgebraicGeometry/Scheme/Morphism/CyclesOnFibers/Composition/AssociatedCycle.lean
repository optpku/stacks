/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle.FiberFamily
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tensor

/-!
# Associated cycle families under composition

Composition of associated fibre-cycle families of quasi-coherent finite-type
modules agrees with the associated family of their tensor with pullback when
the first module is flat over the intermediate base.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace CyclesOnFibers

/-- For locally finite-type morphisms `X ⟶ Y ⟶ S`, if quasi-coherent finite-type
modules `F` on `X` and `G` on `Y` have fibrewise support dimensions at most `r`
over `Y` and `e` over `S`, and `F` is flat over `Y`, then the tensor of `F`
with the pullback of `G` has fibrewise support dimension at most `r + e` over `S`. -/
theorem tensor_fiberModuleSupportDimensionLE {S X Y : Scheme.{u}}
    (p : Y ⟶ S) (f : X ⟶ Y) [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (r : ℕ)
    (hF : f.fiberModuleSupportDimensionLE F r)
    (G : Y.Modules) [G.IsQuasicoherent] [G.IsFiniteType] (e : ℕ)
    (hG : p.fiberModuleSupportDimensionLE G e)
    (hflat : Modules.flatOver F f) :
    (f ≫ p).fiberModuleSupportDimensionLE (F ⊗ (Modules.pullback f).obj G)
      (r + e) := sorry

/-- For locally finite-type morphisms `X ⟶ Y ⟶ S`, quasi-coherent finite-type
modules with fibrewise support bounds `r` and `e`, the first flat over `Y`,
have composite associated fibre-cycle family equal to the degree-`r + e`
associated family of their tensor with pullback. -/
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

/-- At every point of every fibre, composition of the associated fibre-cycle
families of quasi-coherent finite-type modules, the first flat over the
intermediate base, has the same coefficient as the associated family of their
tensor with pullback. -/
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
