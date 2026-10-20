/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection.Regular
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.62.13 (1): in a commutative triangle over a locally Noetherian scheme,
if `Y ⟶ S` is locally of finite type, `Y` is regular, and `X ⟶ S` is a local
complete intersection morphism, then `X ⟶ Y` is a local complete intersection morphism. -/
@[stacks 0FJ2]
#check
  (AlgebraicGeometry.LocallyOfType.isLocalCompleteIntersection_of_regular_of_comp :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ Y) (g : Y ⟶ S) (h : X ⟶ S),
      f ≫ g = h →
      [AlgebraicGeometry.IsLocallyNoetherian S] →
      [AlgebraicGeometry.LocallyOfFiniteType g] →
      [AlgebraicGeometry.Scheme.Regular Y] →
      AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection h →
      AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection f)

/- Lemma 37.62.13 (2): under the same hypotheses, `Y ⟶ S` is Koszul at every
point `f x` in the image of `X`, expressed by the canonical `Scheme.Hom.KoszulAt`
predicate. -/
@[stacks 0FJ2]
#check
  (AlgebraicGeometry.Scheme.Hom.koszulAt_image_of_regular_of_comp :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ Y) (g : Y ⟶ S) (h : X ⟶ S),
      f ≫ g = h →
      [AlgebraicGeometry.IsLocallyNoetherian S] →
      [AlgebraicGeometry.LocallyOfFiniteType g] →
      [AlgebraicGeometry.Scheme.Regular Y] →
      AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection h →
      ∀ x : X, g.KoszulAt (f x))
