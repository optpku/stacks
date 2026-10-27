/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Purity
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 77.3.2: Universal purity is equivalent to purity after every pointed base change. -/
@[stacks 0CVE] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IsUniversallyPureAlong.iff_forall_pointedBaseChange :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y),
    F.IsUniversallyPureAlong f y ↔
      ∀ {Y' : AlgebraicSpace S} (g : Y' ⟶ Y) (y' : Points Y'),
        Points.map g y' = y →
          ((Modules.pullback (pullback.fst f g)).obj F).IsPureAlong
            (pullback.snd f g) y')

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IsUniversallyPureOver.iff_forall_baseChange :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType],
    F.IsUniversallyPureOver f ↔
      ∀ {Y' : AlgebraicSpace S} (g : Y' ⟶ Y),
        ((Modules.pullback (pullback.fst f g)).obj F).IsPureOver
          (pullback.snd f g))

end AlgebraicGeometry.AlgebraicSpace.Modules
