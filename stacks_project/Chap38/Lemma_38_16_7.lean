/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 38.16.7 (1): a finite type quasicoherent module on a closed subscheme is
pure along the fibre over `s` if and only if its pushforward is pure there. -/
@[stacks 05K1] #check
  (AlgebraicGeometry.Scheme.Modules.isPureAlong_pushforward_iff_of_isClosedImmersion :
    ∀ {X Z S : Scheme.{u}} (f : X ⟶ S) [f.FiniteType]
      (i : Z ⟶ X) [IsClosedImmersion i]
      (F : Z.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (s : S),
      F.IsPureAlong (i ≫ f) s ↔
        ((Scheme.Modules.pushforward i).obj F).IsPureAlong f s)

/- Lemma 38.16.7 (2): a finite type quasicoherent module on a closed subscheme is
universally pure along the fibre over `s` if and only if its pushforward is universally
pure there. -/
@[stacks 05K1] #check
  (AlgebraicGeometry.Scheme.Modules.isUniversallyPureAlong_pushforward_iff_of_isClosedImmersion :
    ∀ {X Z S : Scheme.{u}} (f : X ⟶ S) [f.FiniteType]
      (i : Z ⟶ X) [IsClosedImmersion i]
      (F : Z.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (s : S),
      F.IsUniversallyPureAlong (i ≫ f) s ↔
        ((Scheme.Modules.pushforward i).obj F).IsUniversallyPureAlong f s)

end AlgebraicGeometry.Scheme.Modules
