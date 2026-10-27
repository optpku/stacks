/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Purity
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules
namespace IsPureAlong

/-- Purity of a finite type quasi-coherent module along a finite type decent morphism
of algebraic spaces descends from a pointed base change that is flat at the selected
source point. -/
@[stacks 0CVG]
theorem of_pullback_of_flatAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y)
    {Y1 : AlgebraicSpace S} (g : Y1 ⟶ Y) (y1 : Points Y1)
    (hpoint : Points.map g y1 = y) (hflat : FlatAt g y1)
    (hpure : ((Modules.pullback (Limits.pullback.fst f g)).obj F).IsPureAlong
      (Limits.pullback.snd f g) y1) :
    F.IsPureAlong f y :=
  sorry

end IsPureAlong

namespace IsUniversallyPureAlong

/-- Universal purity of a finite type quasi-coherent module along a finite type decent
morphism of algebraic spaces descends from a pointed base change that is flat at the
selected source point. -/
@[stacks 0CVG]
theorem of_pullback_of_flatAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y)
    {Y1 : AlgebraicSpace S} (g : Y1 ⟶ Y) (y1 : Points Y1)
    (hpoint : Points.map g y1 = y) (hflat : FlatAt g y1)
    (hpure : ((Modules.pullback (Limits.pullback.fst f g)).obj F).IsUniversallyPureAlong
      (Limits.pullback.snd f g) y1) :
    F.IsUniversallyPureAlong f y :=
  sorry

end IsUniversallyPureAlong
end AlgebraicGeometry.AlgebraicSpace.Modules
