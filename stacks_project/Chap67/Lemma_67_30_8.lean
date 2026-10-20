/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall

public import Mathlib.RingTheory.RingHom.Flat
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap66.Lemma_66_29_5_Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Flat

/-!
# Flatness at a point via étale local rings

A morphism of algebraic spaces is flat at a point if and only if the induced
map of étale local rings at a geometric point over that point is a flat ring
homomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.30.8: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `xbar` be a geometric point of `X` lying over
the point `x ∈ |X|`. Let `ȳ = xbar.map f`. Then `f` is flat at `x` if and only
if the map of étale local rings `etaleLocalRingMap f xbar : 𝒪_{Y, ȳ} → 𝒪_{X, xbar}`
is flat. -/
@[stacks 04NG]
#check (AlgebraicGeometry.AlgebraicSpace.flatAt_iff_etaleLocalRingMap_flat :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (xbar : GeometricPoint X) (x : Points X) (hx : xbar.liesOver x),
    FlatAt f x ↔ (etaleLocalRingMap f xbar).Flat)

/- Flatness at the image of a geometric point is equivalent to flatness of the
induced étale local ring map. -/
#check (AlgebraicGeometry.AlgebraicSpace.flatAt_iff_etaleLocalRingMap_flat_image :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (xbar : GeometricPoint X),
    FlatAt f xbar.image ↔ (etaleLocalRingMap f xbar).Flat)

end AlgebraicGeometry.AlgebraicSpace
