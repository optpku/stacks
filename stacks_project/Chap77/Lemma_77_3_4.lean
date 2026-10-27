/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Purity.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 77.3.4: In Situation 77.2.1, purity and universal purity above a point
descend along a morphism of pointed algebraic spaces that is flat at the source point. -/
@[stacks 0CVG] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IsPureAlong.of_pullback_of_flatAt :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y)
    {Y1 : AlgebraicSpace S} (g : Y1 ⟶ Y) (y1 : Points Y1)
    (hpoint : Points.map g y1 = y) (hflat : FlatAt g y1)
    (hpure : ((Modules.pullback (Limits.pullback.fst f g)).obj F).IsPureAlong
      (Limits.pullback.snd f g) y1),
    F.IsPureAlong f y)

/- Lemma 77.3.4 (2): Universal purity descends along the same pointed flat base change. -/
@[stacks 0CVG] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IsUniversallyPureAlong.of_pullback_of_flatAt :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y)
    {Y1 : AlgebraicSpace S} (g : Y1 ⟶ Y) (y1 : Points Y1)
    (hpoint : Points.map g y1 = y) (hflat : FlatAt g y1)
    (hpure : ((Modules.pullback (Limits.pullback.fst f g)).obj F).IsUniversallyPureAlong
      (Limits.pullback.snd f g) y1),
    F.IsUniversallyPureAlong f y)
