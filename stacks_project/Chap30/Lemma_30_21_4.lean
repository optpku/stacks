/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback

/-!
# Relative ampleness near a proper fiber over a Noetherian base

For a proper morphism to a Noetherian scheme, an invertible module that is ample
on one scheme-theoretic fibre is relatively ample over some open neighbourhood
of that point.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RelativelyAmple

/-- Lemma 30.21.4: let `f : X ⟶ Y` be a proper morphism of schemes with `Y` Noetherian,
let `L` be an invertible `𝒪_X`-module, and let `y` be a point of `Y` such that the
pullback of `L` to the scheme-theoretic fibre `X_y` is ample. Then there is an open
neighbourhood `V ⊂ Y` of `y` such that the restriction of `L` to `f ⁻¹ᵁ V` is
relatively ample on `f ∣_ V`. (A more general version is Lemma 37.50.3.) -/
@[stacks 0D2N]
theorem exists_morphismRestrict_of_isAmple_fiber_of_isNoetherian
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsNoetherian Y] [IsProper f]
    (L : X.Modules) [L.Invertible] (y : Y)
    [Scheme.Modules.IsAmple ((Scheme.Modules.pullback (f.fiberι y)).obj L)] :
    ∃ V : Y.Opens, y ∈ V ∧ RelativelyAmple (f ∣_ V) (restrictToBasePreimage f L V) :=
  sorry

end AlgebraicGeometry.RelativelyAmple
