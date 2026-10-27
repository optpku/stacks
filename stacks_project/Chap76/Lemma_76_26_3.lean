/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import Mathlib.Data.List.TFAE
public import stacks_project.Chap76.Lemma_76_26_3_CohenMacaulay
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.CohenMacaulay

/-!
# Characterizations of Cohen–Macaulay morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.26.3 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume the fibres of `f` are locally Noetherian.
The following are equivalent: `f` is Cohen–Macaulay; `f` is flat and for some
surjective étale morphism `V ⟶ Y` with `V` a scheme, the fibres of `X_V ⟶ V`
are Cohen–Macaulay algebraic spaces; and `f` is flat and for any étale
morphism `V ⟶ Y` with `V` a scheme, the fibres of `X_V ⟶ V` are Cohen–Macaulay
algebraic spaces. -/
@[stacks 0E0W]
#check (AlgebraicGeometry.AlgebraicSpace.cohenMacaulay_tfae :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyNoetherianFibers f],
    List.TFAE
      [ CohenMacaulay f
      , Flat f ∧
          ∃ (V : Over S) (b : ofOver V ⟶ Y),
            (over (@AlgebraicGeometry.Etale)).presheaf b ∧
              Surjective b ∧ fibersCohenMacaulay f b
      , Flat f ∧
          ∀ (V : Over S) (b : ofOver V ⟶ Y),
            (over (@AlgebraicGeometry.Etale)).presheaf b →
              fibersCohenMacaulay f b ])

/- Lemma 76.26.3 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume the fibres of `f` are locally Noetherian.
Given `x` in `|X|` with image `y = Points.map f x` in `|Y|`, `f` is
Cohen–Macaulay at `x` if and only if
`etaleLocalRingMap f xbar : 𝒪_{Y, ȳ} ⟶ 𝒪_{X, x̄}` is flat and
`fiberEtaleLocalRing f xbar` is a Cohen–Macaulay ring, for a geometric point
`xbar` lying over `x`. -/
@[stacks 0E0W]
#check (AlgebraicGeometry.AlgebraicSpace.cohenMacaulayAt_iff_etaleLocalRing :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyNoetherianFibers f]
    (xbar : GeometricPoint X) (x : Points X) (hx : xbar.liesOver x),
    CohenMacaulayAt f x ↔
      (etaleLocalRingMap f xbar).Flat ∧
        CohenMacaulayRing (fiberEtaleLocalRing f xbar))

end AlgebraicGeometry.AlgebraicSpace
