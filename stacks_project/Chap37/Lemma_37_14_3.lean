/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Pushout.Thickening
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 37.14.3 (1): a thickening and an affine morphism with common source
have a pushout in the category of schemes. -/
@[stacks 07RT] #check
  (AlgebraicGeometry.Scheme.Pushout.instHasPushoutThickeningAffine :
    ∀ {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [IsAffineHom f], HasPushout i f)

/- Lemma 37.14.3 (2): the canonical morphism from the target of the affine
morphism to the pushout is a thickening. -/
@[stacks 07RT] #check
  (AlgebraicGeometry.Scheme.Pushout.instInrIsThickening :
    ∀ {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [IsAffineHom f], IsThickening (pushout.inr i f))

/- Lemma 37.14.3 (3): the canonical pushout square is also cartesian. -/
@[stacks 07RT] #check
  (AlgebraicGeometry.Scheme.Pushout.isPullback :
    ∀ {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [IsAffineHom f],
      IsPullback i f (pushout.inl i f) (pushout.inr i f))

/- Lemma 37.14.3 (4): on every open of the canonical pushout, its section ring
is the pullback of the corresponding section rings on `Y` and `X'` over `X`. -/
@[stacks 07RT] #check
  (AlgebraicGeometry.Scheme.Pushout.structureSheaf_isPullback :
    ∀ {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [IsAffineHom f],
      AlgebraicGeometry.Scheme.Pushout.IsStructureSheafPullback
        (IsPushout.of_hasPushout i f).toCommSq)
