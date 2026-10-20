module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Base change of relatively ample modules on algebraic spaces

Relative ampleness of modules on algebraic spaces is preserved by cartesian base change.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Pulling a relatively ample module back around a cartesian square of algebraic
spaces preserves relative ampleness. -/
theorem RelativelyAmple.of_isPullback {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {L : X.Modules} (sq : IsPullback g' f' f g)
    (hL : RelativelyAmple f L) :
    RelativelyAmple f' ((Modules.pullback g').obj L) :=
  sorry

/-- The pullback of a relatively ample module along the canonical projection is
relatively ample over the other projection. -/
instance RelativelyAmple.pullback {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (L : X.Modules) [hL : RelativelyAmple f L] :
    RelativelyAmple (pullback.snd f g)
      ((Modules.pullback (pullback.fst f g)).obj L) :=
  RelativelyAmple.of_isPullback (IsPullback.of_hasPullback f g) hL

end AlgebraicGeometry.AlgebraicSpace
