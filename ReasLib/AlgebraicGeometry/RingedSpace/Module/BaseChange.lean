/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Composition
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change for modules on ringed spaces

The module base-change transformation for a commutative square of ringed spaces is the mate of
the canonical pullback-composition isomorphism.  This file owns both the pullback square and its
right mate; derived specializations live in separate leaves.
-/

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.BaseChange

/-- The canonical square of module pullbacks attached to a commutative square of ringed spaces. -/
@[stacks 02N7 "underived module pullback square"]
noncomputable def pullbackIso
    {X X' S S' : RingedSpace.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (sq : CommSq g' f' f g) :
    pullback g ⋙ pullback f' ≅ pullback f ⋙ pullback g' :=
  (RingedSpace.Hom.pullbackCompIso f' g).symm ≪≫
    eqToIso (congrArg RingedSpace.Hom.pullback sq.w.symm) ≪≫
      RingedSpace.Hom.pullbackCompIso g' f

/-- The canonical underived module base-change transformation attached to a commutative square
of ringed spaces. -/
@[stacks 02N7 "underived module base-change transformation"]
noncomputable def map
    {X X' S S' : RingedSpace.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (sq : CommSq g' f' f g) :
    (pushforward f ⋙ pullback g) ⟶ (pullback g' ⋙ pushforward f') :=
  (mateEquiv
    (RingedSpace.Hom.pullbackPushforwardAdjunction f)
    (RingedSpace.Hom.pullbackPushforwardAdjunction f')
    (pullbackIso sq).hom).natTrans

end AlgebraicGeometry.RingedSpace.Hom.BaseChange
