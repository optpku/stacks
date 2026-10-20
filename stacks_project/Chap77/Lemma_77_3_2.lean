/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap77.Lemma_77_3_2_Purity

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules
namespace IsUniversallyPureAlong

/-- Lemma 77.3.2: In Situation 77.2.1, `F` is universally pure above `y` if and only if
for every morphism of pointed algebraic spaces `(Y', y') ⟶ (Y, y)` the pullback of `F`
to `X ×_Y Y'` is pure above `y'`. -/
@[stacks 0CVE]
theorem iff_forall_pointedBaseChange {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y) :
    F.IsUniversallyPureAlong f y ↔
      ∀ {Y' : AlgebraicSpace S} (g : Y' ⟶ Y) (y' : Points Y'),
        Points.map g y' = y →
          ((Modules.pullback (pullback.fst f g)).obj F).IsPureAlong
            (pullback.snd f g) y' :=
  sorry

end IsUniversallyPureAlong

namespace IsUniversallyPureOver

/-- In Situation 77.2.1, `F` is universally pure relative to `Y` if and only if every
base change of `F` is pure relative to the new base. -/
theorem iff_forall_baseChange {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] :
    F.IsUniversallyPureOver f ↔
      ∀ {Y' : AlgebraicSpace S} (g : Y' ⟶ Y),
        ((Modules.pullback (pullback.fst f g)).obj F).IsPureOver
          (pullback.snd f g) :=
  sorry

end IsUniversallyPureOver
end AlgebraicGeometry.AlgebraicSpace.Modules
