/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Cap.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Pullback.OverMap

/-!
# Base change of composition of families of cycles on fibres

Fibrewise composition of cycle families commutes with arbitrary base change.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.CyclesOnFibers

/-- The canonical identification between the fibres of the two projections
from the base change of a composite morphism. -/
noncomputable def compBaseChangeFiberMap {S S' X Y : Scheme.{u}}
    (g : S' ⟶ S) (p : Y ⟶ S) (f : X ⟶ Y) (s' : S') :
    (Scheme.Pullback.overMap g p f ≫ pullback.snd p g).fiber s' ⟶
      (pullback.snd (f ≫ p) g).fiber s' :=
  eqToHom (congrArg (fun q : pullback (f ≫ p) g ⟶ S' => q.fiber s')
    (Scheme.Pullback.overMap_comp_snd g p f))

/-- The composition of families of nonnegative-degree cycles on fibres
commutes with arbitrary base change. -/
theorem comp_baseChange {S S' X Y : Scheme.{u}} (g : S' ⟶ S) (p : Y ⟶ S)
    (f : X ⟶ Y) [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    {r e : ℤ} (hr : 0 ≤ r) (he : 0 ≤ e)
    (α : CyclesOnFibers f r) (β : CyclesOnFibers p e) (s' : S')
    (x' : (Scheme.Pullback.overMap g p f ≫ pullback.snd p g).fiber s') :
    toAlgebraicCycle
        (comp (FiberCycleFamily.baseChange
          (Scheme.Pullback.isPullback_overMap g p f) α)
          (FiberCycleFamily.baseChange (IsPullback.of_hasPullback p g) β))
        s' x' =
      toAlgebraicCycle
        (FiberCycleFamily.baseChange
          (IsPullback.of_hasPullback (f ≫ p) g) (comp α β))
        s' (compBaseChangeFiberMap g p f s' x') := by
  sorry

end AlgebraicGeometry.Scheme.Hom.CyclesOnFibers
