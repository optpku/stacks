/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection.Perfect
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.62.12 (1): in a commutative triangle over a locally Noetherian scheme,
if `Y ⟶ S` is locally of finite type, `X ⟶ Y` is perfect, and `X ⟶ S` is a local complete
intersection morphism, then `X ⟶ Y` is a local complete intersection morphism. -/
@[stacks 09RL]
#check
  (AlgebraicGeometry.LocallyOfType.isLocalCompleteIntersection_of_perfect_of_comp :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ Y) (g : Y ⟶ S) (h : X ⟶ S),
      f ≫ g = h →
      [AlgebraicGeometry.IsLocallyNoetherian S] →
      [AlgebraicGeometry.LocallyOfFiniteType g] →
      AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap f →
      AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection h →
      AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection f)

/- Lemma 37.62.12 (2): under the same hypotheses, `Y ⟶ S` is Koszul at every point `f x` in
the image of `X`. -/
@[stacks 09RL]
#check
  (AlgebraicGeometry.Scheme.Hom.koszulAt_image_of_perfect_of_comp :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ Y) (g : Y ⟶ S) (h : X ⟶ S),
      f ≫ g = h →
      [AlgebraicGeometry.IsLocallyNoetherian S] →
      [AlgebraicGeometry.LocallyOfFiniteType g] →
      AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap f →
      AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection h →
      ∀ x : X, g.KoszulAt (f x))
