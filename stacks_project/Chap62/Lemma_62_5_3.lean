/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle.FiberFamily.Operations

/-!
# Compatibility of associated module cycle families

The associated fibrewise cycle family of a quasi-coherent finite-type module
commutes with base change, restriction, and flat pullback.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 62.5.3 (1): the associated module cycle family commutes with
base change. -/
@[stacks 0H4R] #check
  (AlgebraicGeometry.Scheme.Hom.moduleFiberCycleFamily_baseChange :
    ∀ {S X S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (hpb : IsPullback g' f' f g)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (r : ℕ)
    (hF : f.fiberModuleSupportDimensionLE F r),
    FiberCycleFamily.baseChange hpb (moduleFiberCycleFamily f F r hF) =
      moduleFiberCycleFamily f' ((Modules.pullback g').obj F) r
        (fiberModuleSupportDimensionLE_baseChange hpb F r hF))

/- Lemma 62.5.3 (2): the associated module cycle family commutes with
restriction to compatible opens. -/
@[stacks 0H4R] #check
  (AlgebraicGeometry.Scheme.Hom.moduleFiberCycleFamily_restrict :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
    (U : X.Opens) (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V) (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (r : ℕ)
    (hF : f.fiberModuleSupportDimensionLE F r),
    FiberCycleFamily.restrict U V hU (moduleFiberCycleFamily f F r hF) =
      moduleFiberCycleFamily (f.resLE V U hU) ((Modules.pullback U.ι).obj F) r
        (fiberModuleSupportDimensionLE_restrict U V hU F r hF))

/- Lemma 62.5.3 (3): the associated module cycle family commutes with
flat pullback. -/
@[stacks 0H4R] #check
  (AlgebraicGeometry.Scheme.Hom.moduleFiberCycleFamily_flatPullback :
    ∀ {X' X S : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (h : X' ⟶ X)
    (hf : h ≫ f = f') (e : ℕ) [Flat h] [RelativeDimension h e]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (r : ℕ)
    (hF : f.fiberModuleSupportDimensionLE F r),
    FiberCycleFamily.flatPullback h hf e (moduleFiberCycleFamily f F r hF) =
      FiberCycleFamily.reindex (Int.natCast_add r e)
        (moduleFiberCycleFamily f' ((Modules.pullback h).obj F) (r + e)
          (fiberModuleSupportDimensionLE_flatPullback h hf e F r hF)))

end AlgebraicGeometry.Scheme.Hom
