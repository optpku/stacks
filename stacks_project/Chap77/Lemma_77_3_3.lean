/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Purity
import StacksCheckRecall

/-!
# Quasi-finite pointed base change of purity on algebraic spaces

Purity of a finite type quasi-coherent module above a selected point is preserved
by a pointed base change that is quasi-finite at the source point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 77.3.3: Purity above a point is preserved by quasi-finite pointed base change. -/
@[stacks 0CVF] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IsPureAlong.pullback_of_quasiFiniteAt :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FiniteType f] [Decent f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (y : |Y|) {Y' : AlgebraicSpace S}
    (g : Y' ⟶ Y) (y' : |Y'|) (hpoint : Points.map g y' = y)
    (hquasi : FiniteType.QuasiFiniteAt g y') (hpure : IsPureAlong F f y),
    IsPureAlong ((pullback (Limits.pullback.fst f g)).obj F)
      (Limits.pullback.snd f g) y')

end AlgebraicGeometry.AlgebraicSpace.Modules
