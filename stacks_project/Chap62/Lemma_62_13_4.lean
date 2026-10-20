/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Composition.AssociatedCycle
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Hom.CyclesOnFibers

/- Lemma 62.13.4: Composition of the associated fibre-cycle families of two
quasi-coherent finite-type modules, with the first flat over the intermediate
base, equals the associated family of their tensor with pullback. -/
@[stacks 0H6L] #check
  (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.comp_moduleFiberCycleFamily :
    ∀ {S X Y : Scheme.{u}}
    (p : Y ⟶ S) (f : X ⟶ Y) [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (r : ℕ)
    (hF : f.fiberModuleSupportDimensionLE F r)
    (G : Y.Modules) [G.IsQuasicoherent] [G.IsFiniteType] (e : ℕ)
    (hG : p.fiberModuleSupportDimensionLE G e)
    (hflat : Modules.flatOver F f),
    comp (moduleFiberCycleFamily f F r hF) (moduleFiberCycleFamily p G e hG) =
      FiberCycleFamily.reindex (Int.natCast_add r e)
        (moduleFiberCycleFamily (f ≫ p) (F ⊗ (Modules.pullback f).obj G)
          (r + e)
          (tensor_fiberModuleSupportDimensionLE p f F r hF G e hG hflat)))

end AlgebraicGeometry.Scheme.Hom.CyclesOnFibers
