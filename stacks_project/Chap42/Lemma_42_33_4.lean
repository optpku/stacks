/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.BivariantClass.ProperPushforward

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 42.33.4: Proper pushforward sends a bivariant class `c` to the
bivariant class `properPushforward δ f g p c`, whose cap map is `c.cap` followed
by Chow pushforward along the base change of `f`. -/
@[stacks 0EPK] #check
  (AlgebraicGeometry.BivariantClass.properPushforward :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      {X Y T : Over S} [AlgebraicGeometry.LocallyOfFiniteType X.hom]
      [AlgebraicGeometry.LocallyOfFiniteType Y.hom]
      [AlgebraicGeometry.LocallyOfFiniteType T.hom] (f : X ⟶ Y)
      [AlgebraicGeometry.IsProper f.left] (g : Y ⟶ T) (p : ℤ)
      (c : AlgebraicGeometry.BivariantClass δ (f ≫ g) p),
      AlgebraicGeometry.BivariantClass δ g p)

#check
  (AlgebraicGeometry.BivariantClass.properPushforward_cap :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      {X Y T Y' T' : Over S} [AlgebraicGeometry.LocallyOfFiniteType X.hom]
      [AlgebraicGeometry.LocallyOfFiniteType Y.hom]
      [AlgebraicGeometry.LocallyOfFiniteType T.hom]
      [AlgebraicGeometry.LocallyOfFiniteType Y'.hom]
      [AlgebraicGeometry.LocallyOfFiniteType T'.hom] (f : X ⟶ Y)
      [AlgebraicGeometry.IsProper f.left] (g : Y ⟶ T) (p : ℤ)
      (c : AlgebraicGeometry.BivariantClass δ (f ≫ g) p)
      (i : Y' ⟶ Y) (g' : Y' ⟶ T') (h : T' ⟶ T)
      [AlgebraicGeometry.LocallyOfFiniteType h.left]
      (square : IsPullback i.left g'.left g.left h.left) (k : ℤ),
      (AlgebraicGeometry.BivariantClass.properPushforward δ f g p c).cap
          i g' h square k =
        (AlgebraicGeometry.ChowGroup.map δ (pullback f i) Y' (pullback.snd f i)
          (k - p)).comp
          (c.cap (pullback.fst f i) (pullback.snd f i ≫ g') h
            (AlgebraicGeometry.BivariantClass.properPushforwardSquare
              f g i g' h square) k))
