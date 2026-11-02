/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup

/-!
# Normalized blowups of algebraic spaces at closed points

A normalized blowup of a decent algebraic space at a closed point is an ordinary
point blowup, followed by the canonical absolute normalization of its source.
The ordinary center is the residue-field closed subspace representing that point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace NormalizedBlowup

/-- The residue-field closed subspace representing a closed point of a decent algebraic
space, used as the ordinary blowup center. -/
noncomputable def closedPointCenter {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (x : Points X) (hx : x ∈ closedPoints (Points X)) : ClosedSubspace X :=
  { X := ofOver (FieldValuedPoint.residuePoint x).overObj
    ι := X.fromSpecResidueField x
    isClosedImmersion := isClosedImmersion_fromSpecResidueField hx }

/-- The inclusion of the residue-field closed subspace is the residue-field morphism. -/
theorem closedPointCenter_ι {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (x : Points X) (hx : x ∈ closedPoints (Points X)) :
    (closedPointCenter x hx).ι = X.fromSpecResidueField x :=
  rfl

end NormalizedBlowup

/-- A normalized blowup of `X` at a closed point: a chosen ordinary blowup of `X` at
that point, together with a finite-components witness making the absolute
normalization of the ordinary blowup space available. -/
structure NormalizedBlowup {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] : Type (u + 1) where
  /-- The closed point blown up. -/
  point : Points X
  /-- The chosen point is closed in `Points X`. -/
  isClosedPoint : point ∈ closedPoints (Points X)
  /-- The source algebraic space of the ordinary blowup before normalization. -/
  blowupSpace : AlgebraicSpace S
  /-- The ordinary blowup morphism. -/
  toBlowup : blowupSpace ⟶ X
  /-- The ordinary morphism is the blowup at the residue-field closed subspace of the
  chosen closed point. -/
  isBlowup : IsBlowup toBlowup (NormalizedBlowup.closedPointCenter point isClosedPoint)
  /-- The ordinary blowup space has finitely many irreducible components on compact opens,
  so its absolute normalization is defined. -/
  finiteComponents : HasFiniteIrreducibleComponentsOnCompactOpens blowupSpace

namespace NormalizedBlowup

/-- Construct a normalized blowup from an ordinary closed-point blowup and the finite-components
witness for its source. -/
def of {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (point : Points X) (isClosedPoint : point ∈ closedPoints (Points X))
    (blowupSpace : AlgebraicSpace S) (toBlowup : blowupSpace ⟶ X)
    (isBlowup : IsBlowup toBlowup (closedPointCenter point isClosedPoint))
    (finiteComponents : HasFiniteIrreducibleComponentsOnCompactOpens blowupSpace) :
    NormalizedBlowup X :=
  { point, isClosedPoint, blowupSpace, toBlowup, isBlowup, finiteComponents }

/-- The closed point of a normalized blowup constructed by `of` is the supplied point. -/
theorem of_point {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (point : Points X) (isClosedPoint : point ∈ closedPoints (Points X))
    (blowupSpace : AlgebraicSpace S) (toBlowup : blowupSpace ⟶ X)
    (isBlowup : IsBlowup toBlowup (closedPointCenter point isClosedPoint))
    (finiteComponents : HasFiniteIrreducibleComponentsOnCompactOpens blowupSpace) :
    (of point isClosedPoint blowupSpace toBlowup isBlowup finiteComponents).point = point :=
  rfl

/-- The ordinary blowup morphism of a normalized blowup constructed by `of` is the supplied
morphism. -/
theorem of_toBlowup {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (point : Points X) (isClosedPoint : point ∈ closedPoints (Points X))
    (blowupSpace : AlgebraicSpace S) (toBlowup : blowupSpace ⟶ X)
    (isBlowup : IsBlowup toBlowup (closedPointCenter point isClosedPoint))
    (finiteComponents : HasFiniteIrreducibleComponentsOnCompactOpens blowupSpace) :
    (of point isClosedPoint blowupSpace toBlowup isBlowup finiteComponents).toBlowup =
      toBlowup :=
  rfl

/-- The source of a normalized blowup is the canonical normalization of the ordinary blowup
space. -/
noncomputable def source {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (s : NormalizedBlowup X) : AlgebraicSpace S :=
  @normalization _ s.blowupSpace s.finiteComponents

/-- The source accessor uses the stored finite-components witness on the ordinary blowup. -/
theorem source_eq {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] (s : NormalizedBlowup X) :
    s.source = @normalization _ s.blowupSpace s.finiteComponents :=
  rfl

/-- The normalization morphism from the normalized source to the ordinary blowup space. -/
noncomputable def toNormalization {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (s : NormalizedBlowup X) : s.source ⟶ s.blowupSpace :=
  @normalizationTo _ s.blowupSpace s.finiteComponents

/-- The normalization morphism accessor is the canonical absolute normalization morphism. -/
theorem toNormalization_def {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] (s : NormalizedBlowup X) :
    s.toNormalization = @normalizationTo _ s.blowupSpace s.finiteComponents :=
  rfl

/-- The normalized blowup morphism, obtained by normalization followed by the ordinary blowup. -/
noncomputable def hom {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (s : NormalizedBlowup X) : s.source ⟶ X :=
  s.toNormalization ≫ s.toBlowup

/-- A normalized blowup morphism is the normalization morphism followed by the ordinary point
blowup. -/
theorem hom_def {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] (s : NormalizedBlowup X) :
    s.hom = s.toNormalization ≫ s.toBlowup :=
  rfl

/-- A normalized blowup is a closed-point ordinary blowup of `X`, followed by absolute
normalization of that blowup space. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] (s : NormalizedBlowup X) :
    s.point ∈ closedPoints (Points X) ∧
      IsBlowup s.toBlowup (closedPointCenter s.point s.isClosedPoint) ∧
      s.source = @normalization _ s.blowupSpace s.finiteComponents ∧
      s.hom = s.toNormalization ≫ s.toBlowup :=
  ⟨s.isClosedPoint, s.isBlowup, s.source_eq, s.hom_def⟩

end NormalizedBlowup

end AlgebraicGeometry.AlgebraicSpace
