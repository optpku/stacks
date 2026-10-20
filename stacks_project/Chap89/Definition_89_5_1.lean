/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Normalized
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 89.5.1: Let `S` be a scheme. Let `X` be a decent algebraic space over `S`
satisfying the equivalent conditions of Morphisms of Spaces, Lemma 67.49.1. Let `x ∈ |X|`
be a closed point. The normalized blowup of `X` at `x` is the composition `X'' ⟶ X' ⟶ X`
where `X' ⟶ X` is the blowup of `X` at `x` (Definition 89.4.1) and `X'' ⟶ X'` is the
normalization of `X'`. -/
@[stacks 0BHJ] #check (AlgebraicGeometry.AlgebraicSpace.NormalizedBlowup :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X], Type (u + 1))
#check (AlgebraicGeometry.AlgebraicSpace.NormalizedBlowup.of :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (point : Points X) (isClosedPoint : point ∈ closedPoints (Points X))
    (blowupSpace : AlgebraicSpace S) (toBlowup : blowupSpace ⟶ X),
    IsBlowup toBlowup (NormalizedBlowup.closedPointCenter point isClosedPoint) →
    HasFiniteIrreducibleComponentsOnCompactOpens blowupSpace → NormalizedBlowup X)
#check (AlgebraicGeometry.AlgebraicSpace.NormalizedBlowup.hom :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] (s : NormalizedBlowup X),
    s.source ⟶ X)
#check (AlgebraicGeometry.AlgebraicSpace.NormalizedBlowup.source :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X],
    NormalizedBlowup X → AlgebraicSpace S)
#check (AlgebraicGeometry.AlgebraicSpace.NormalizedBlowup.spec :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] (s : NormalizedBlowup X),
    s.point ∈ closedPoints (Points X) ∧
      IsBlowup s.toBlowup (NormalizedBlowup.closedPointCenter s.point s.isClosedPoint) ∧
      s.source = @normalization _ s.blowupSpace s.finiteComponents ∧
      s.hom = s.toNormalization ≫ s.toBlowup)
