/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RelativePurity

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Lemma 38.16.3: universal purity along a fibre is equivalent to purity after every
pointed base change. -/
@[stacks 05J6] #check
  (AlgebraicGeometry.Scheme.Modules.IsUniversallyPureAlong.iff_forall_pointedBaseChange :
    ∀ {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
      [f.FiniteType] [F.IsQuasicoherent] [F.IsFiniteType] (s : S),
      F.IsUniversallyPureAlong f s ↔
        ∀ {S' : Scheme.{u}} (g : S' ⟶ S) (s' : S'), g s' = s →
          ((Scheme.Modules.pullback (pullback.fst f g)).obj F).IsPureAlong
            (pullback.snd f g) s')

/- Universal relative purity is equivalent to relative purity after every base change. -/
#check
  (AlgebraicGeometry.Scheme.Modules.IsUniversallyPureOver.iff_forall_baseChange :
    ∀ {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
      [f.FiniteType] [F.IsQuasicoherent] [F.IsFiniteType],
      F.IsUniversallyPureOver f ↔
        ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
          ((Scheme.Modules.pullback (pullback.fst f g)).obj F).IsPureOver
            (pullback.snd f g))

end AlgebraicGeometry
