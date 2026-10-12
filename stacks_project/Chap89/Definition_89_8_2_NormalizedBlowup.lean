/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_49_5_Normalization
public import stacks_project.Chap68.Lemma_68_14_6
public import stacks_project.Chap71.Lemma_71_19_3_AdmissibleBlowup

/-!
# Normalized blowups of algebraic spaces at closed points

A normalized blowup of a decent algebraic space at a closed point is an
ordinary point blowup, followed by the canonical absolute normalization of
its source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ClosedSubspace

/-- The residue-field closed subspace representing a closed point of a decent algebraic space. -/
noncomputable def ofResidueField {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (x : Points X) (hx : x ∈ closedPoints (Points X)) : ClosedSubspace X where
  X := ofOver (FieldValuedPoint.residuePoint x).overObj
  ι := X.fromSpecResidueField x
  isClosedImmersion := isClosedImmersion_fromSpecResidueField hx

/-- The inclusion of the residue-field closed subspace is the residue-field morphism. -/
theorem ofResidueField_ι {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (x : Points X) (hx : x ∈ closedPoints (Points X)) :
    (ofResidueField x hx).ι = X.fromSpecResidueField x :=
  sorry

end ClosedSubspace

/-- A normalized blowup of `X` at a closed point: an ordinary point blowup together with the
normalization prerequisites for its source. -/
structure NormalizedBlowup {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] :
    Type (u + 1) where
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
  isBlowup : IsBlowup toBlowup (ClosedSubspace.ofResidueField point isClosedPoint)
  /-- The ordinary blowup space has finitely many irreducible components on compact opens,
  so its absolute normalization is defined. -/
  finiteComponents : HasFiniteIrreducibleComponentsOnCompactOpens blowupSpace

namespace NormalizedBlowup

/-- Construct a normalized blowup from an ordinary closed-point blowup and the prerequisites for
its normalization. -/
def of {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (point : Points X) (isClosedPoint : point ∈ closedPoints (Points X))
    (blowupSpace : AlgebraicSpace S) (toBlowup : blowupSpace ⟶ X)
    (isBlowup : IsBlowup toBlowup (ClosedSubspace.ofResidueField point isClosedPoint))
    (finiteComponents : HasFiniteIrreducibleComponentsOnCompactOpens blowupSpace) :
    NormalizedBlowup X :=
  { point, isClosedPoint, blowupSpace, toBlowup, isBlowup, finiteComponents }

/-- The closed point of a normalized blowup constructed by `of` is the supplied point. -/
theorem of_point {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (point : Points X) (isClosedPoint : point ∈ closedPoints (Points X))
    (blowupSpace : AlgebraicSpace S) (toBlowup : blowupSpace ⟶ X)
    (isBlowup : IsBlowup toBlowup (ClosedSubspace.ofResidueField point isClosedPoint))
    (finiteComponents : HasFiniteIrreducibleComponentsOnCompactOpens blowupSpace) :
    (of point isClosedPoint blowupSpace toBlowup isBlowup finiteComponents).point = point :=
  sorry

/-- The source of a normalized blowup is the canonical normalization of the ordinary blowup
space. -/
noncomputable def source {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (s : NormalizedBlowup X) : AlgebraicSpace S :=
  @normalization _ s.blowupSpace s.finiteComponents

/-- The source accessor uses the stored normalization prerequisites. -/
theorem source_eq {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (s : NormalizedBlowup X) :
    s.source = @normalization _ s.blowupSpace s.finiteComponents :=
  sorry

/-- The normalization morphism from the normalized source to the ordinary blowup space. -/
noncomputable def toNormalization {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (s : NormalizedBlowup X) : s.source ⟶ s.blowupSpace :=
  @normalizationTo _ s.blowupSpace s.finiteComponents

/-- The normalization morphism accessor is the canonical absolute normalization morphism. -/
theorem toNormalization_def {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (s : NormalizedBlowup X) :
    s.toNormalization = @normalizationTo _ s.blowupSpace s.finiteComponents :=
  sorry

/-- The normalized blowup morphism, obtained by normalization followed by the ordinary blowup. -/
noncomputable def hom {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (s : NormalizedBlowup X) : s.source ⟶ X :=
  s.toNormalization ≫ s.toBlowup

/-- A normalized blowup morphism is the normalization morphism followed by the ordinary point
blowup. -/
theorem hom_def {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (s : NormalizedBlowup X) : s.hom = s.toNormalization ≫ s.toBlowup :=
  sorry

end NormalizedBlowup

end AlgebraicGeometry.AlgebraicSpace
