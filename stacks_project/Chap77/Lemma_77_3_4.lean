/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap77.Lemma_77_3_2_Purity
public import stacks_project.Chap67.Lemma_67_30_5_Flat

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules
namespace IsPureAlong

/-- Lemma 77.3.4 (1): In Situation 77.2.1, let `(Y1, y1) ⟶ (Y, y)` be a morphism of
pointed algebraic spaces that is flat at `y1`. If the pullback of `F` to `X ×_Y Y1`
is pure above `y1`, then `F` is pure above `y`. -/
@[stacks 0CVG]
theorem of_pullback_of_flatAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y)
    {Y1 : AlgebraicSpace S} (g : Y1 ⟶ Y) (y1 : Points Y1)
    (hpoint : Points.map g y1 = y) (hflat : FlatAt g y1)
    (hpure : ((Modules.pullback (pullback.fst f g)).obj F).IsPureAlong
      (pullback.snd f g) y1) :
    F.IsPureAlong f y :=
  sorry

end IsPureAlong

namespace IsUniversallyPureAlong

/-- Lemma 77.3.4 (2): In Situation 77.2.1, let `(Y1, y1) ⟶ (Y, y)` be a morphism of
pointed algebraic spaces that is flat at `y1`. If the pullback of `F` to `X ×_Y Y1`
is universally pure above `y1`, then `F` is universally pure above `y`. -/
@[stacks 0CVG]
theorem of_pullback_of_flatAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y)
    {Y1 : AlgebraicSpace S} (g : Y1 ⟶ Y) (y1 : Points Y1)
    (hpoint : Points.map g y1 = y) (hflat : FlatAt g y1)
    (hpure : ((Modules.pullback (pullback.fst f g)).obj F).IsUniversallyPureAlong
      (pullback.snd f g) y1) :
    F.IsUniversallyPureAlong f y :=
  sorry

end IsUniversallyPureAlong
end AlgebraicGeometry.AlgebraicSpace.Modules
