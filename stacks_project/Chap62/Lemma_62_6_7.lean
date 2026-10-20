/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Module
import StacksCheckRecall

/-!
# Associated module families as relative cycles

This file records that the fibrewise associated-cycle family of a quasi-coherent
finite-type module is a relative cycle when the module is flat over the base in
sufficiently large dimensions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 62.6.7: in the situation of Example 62.5.2, if `S` is locally Noetherian
and `F` is flat over `S` in dimensions `≥ r` in the sense of
`Modules.flatOverInDimensionsGE` (More on Flatness, Definition 38.20.10), then
the associated fibrewise family `moduleFiberCycleFamily f F r hF` is a relative
`r`-cycle on `X / S`. -/
@[stacks 0H56] #check (AlgebraicGeometry.Scheme.Hom.moduleFiberCycleFamily_isRelative :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (r : ℕ)
    (hF : f.fiberModuleSupportDimensionLE F r)
    (hflat : Modules.flatOverInDimensionsGE F f r),
    RelativeCycle.IsRelative (AlgebraicGeometry.Scheme.Hom.moduleFiberCycleFamily f F r hF))

/- The associated fibrewise family of a quasi-coherent finite-type module that is
flat over `S` in dimensions `≥ r` lies in the group `z(X/S, r)` of relative
`r`-cycles. -/
#check (AlgebraicGeometry.Scheme.Hom.moduleFiberCycleFamily_mem_group :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (r : ℕ)
    (hF : f.fiberModuleSupportDimensionLE F r)
    (hflat : Modules.flatOverInDimensionsGE F f r),
    AlgebraicGeometry.Scheme.Hom.moduleFiberCycleFamily f F r hF ∈ RelativeCycle.group f r)

end AlgebraicGeometry.Scheme.Hom
