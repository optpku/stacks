/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Gorenstein.Flat
import StacksCheckRecall

/-!
# Flat morphisms from Gorenstein algebraic spaces

A flat morphism of locally Noetherian algebraic spaces with Gorenstein source is
Gorenstein, and the étale local ring of the target at the image of every
geometric point of the source is a Gorenstein local ring.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 76.27.5 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a flat morphism of
locally Noetherian algebraic spaces over `S`. If `X` is Gorenstein, then `f` is
Gorenstein. -/
@[stacks 0E17]
#check (AlgebraicGeometry.AlgebraicSpace.Gorenstein.of_flat_of_source :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat f] [IsGorenstein X],
    Gorenstein f)

/- Lemma 76.27.5 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a flat morphism of
locally Noetherian algebraic spaces over `S`. If `X` is Gorenstein, then
`𝒪_{Y, f(x̄)}`, that is `etaleLocalRing Y (xbar.map f)`, is a Gorenstein local
ring for every geometric point `x̄` of `X`. -/
@[stacks 0E17]
#check (AlgebraicGeometry.AlgebraicSpace.IsGorenstein.instTargetEtaleLocalRingOfFlat :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat f]
    [IsGorenstein X] (xbar : GeometricPoint X),
    IsGorensteinLocalRing (etaleLocalRing Y (xbar.map f)))
