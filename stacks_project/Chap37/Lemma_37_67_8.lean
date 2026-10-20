/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Pushout.ClosedImmersion.MayerVietoris

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 37.67.8 (1): the pushout of two closed immersions of schemes exists. -/
@[stacks 0B7M] #check
  (AlgebraicGeometry.Scheme.Pushout.ClosedImmersion.instHasPushout :
    ∀ {Z X Y : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
      [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsClosedImmersion j],
      HasPushout i j)

/- Lemma 37.67.8 (2): the canonical pushout square is a fibre square. -/
@[stacks 0B7M] #check
  (AlgebraicGeometry.Scheme.Pushout.ClosedImmersion.isPullback :
    ∀ {Z X Y : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
      [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsClosedImmersion j],
      IsPullback i j (pushout.inl i j) (pushout.inr i j))

/- Lemma 37.67.8 (3): the first canonical coprojection is a closed immersion. -/
@[stacks 0B7M] #check
  (AlgebraicGeometry.Scheme.Pushout.ClosedImmersion.instInlIsClosedImmersion :
    ∀ {Z X Y : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
      [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsClosedImmersion j],
      AlgebraicGeometry.IsClosedImmersion (pushout.inl i j))

/- Lemma 37.67.8 (4): the second canonical coprojection is a closed immersion. -/
@[stacks 0B7M] #check
  (AlgebraicGeometry.Scheme.Pushout.ClosedImmersion.instInrIsClosedImmersion :
    ∀ {Z X Y : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
      [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsClosedImmersion j],
      AlgebraicGeometry.IsClosedImmersion (pushout.inr i j))

/- Lemma 37.67.8 (5): for `c = i ≫ pushout.inl i j = j ≫ pushout.inr i j`,
the canonical structure-module Mayer–Vietoris sequence ending in `c_*𝒪_Z` is short exact. -/
@[stacks 0B7M] #check
  (AlgebraicGeometry.Scheme.Pushout.ClosedImmersion.structureSheafShortExact :
    ∀ {Z X Y : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
      [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsClosedImmersion j],
      (AlgebraicGeometry.Scheme.Pushout.ClosedImmersion.structureSheafShortComplex i j).ShortExact)
