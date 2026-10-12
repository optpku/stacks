/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Pushout.AdmissibleSpan.Existence

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan

/- Proposition 37.67.3 (1): an admissible span has a pushout in the category of schemes. -/
@[stacks 0E25] #check
  (AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.instHasPushout :
    ∀ {S : Scheme.{u}} {Z X Y : Over S} (i : Z ⟶ X) (j : Z ⟶ Y)
        [IsAdmissibleSpan i j],
      HasPushout i.left j.left)

/- Proposition 37.67.3 (2): the canonical pushout square of an admissible span is also a
fibre square. -/
@[stacks 0E25] #check
  (AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.isPullback :
    ∀ {S : Scheme.{u}} {Z X Y : Over S} (i : Z ⟶ X) (j : Z ⟶ Y)
        [IsAdmissibleSpan i j],
      IsPullback i.left j.left (pushout.inl i.left j.left) (pushout.inr i.left j.left))

/- Proposition 37.67.3 (3): the canonical morphism from `X` to the pushout is integral. -/
@[stacks 0E25] #check
  (AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.instInlIsIntegralHom :
    ∀ {S : Scheme.{u}} {Z X Y : Over S} (i : Z ⟶ X) (j : Z ⟶ Y)
        [IsAdmissibleSpan i j],
      IsIntegralHom (pushout.inl i.left j.left))

/- Proposition 37.67.3 (4): the canonical morphism from `Y` to the pushout is a closed
immersion. -/
@[stacks 0E25] #check
  (AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.instInrIsClosedImmersion :
    ∀ {S : Scheme.{u}} {Z X Y : Over S} (i : Z ⟶ X) (j : Z ⟶ Y)
        [IsAdmissibleSpan i j],
      IsClosedImmersion (pushout.inr i.left j.left))

/- Proposition 37.67.3 (5): the structure sheaf on the pushout is the canonical pullback
of the pushed-forward structure sheaves on `Y` and `X` over `Z`. -/
@[stacks 0E25] #check
  (AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.structureSheaf_isPullback :
    ∀ {S : Scheme.{u}} {Z X Y : Over S} (i : Z ⟶ X) (j : Z ⟶ Y)
        [IsAdmissibleSpan i j],
      IsStructureSheafPullback (IsPushout.of_hasPushout i.left j.left).toCommSq)

end AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan
