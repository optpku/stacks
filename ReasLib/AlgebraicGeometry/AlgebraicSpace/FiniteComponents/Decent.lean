module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.CodimensionZero
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.FiniteAbove
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reasonable

/-!
# Decency and finite irreducible components

Decency with finitely many irreducible components is characterized by
quasi-compact étale schemes and by dense open schemes with quasi-compact
generic-point morphisms. These conditions imply reasonableness.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For an algebraic space, decency with finitely many irreducible components
is equivalent to the quasi-compact étale scheme component test with finitely
many monomorphic codimension-zero points, and to the existence of a dense open
scheme with finitely many irreducible components whose generic points have
quasi-compact field-valued representatives in the ambient space. -/
theorem isDecent_finiteIrreducibleComponents_tfae {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    List.TFAE
      [ IsDecent X ∧ HasFiniteIrreducibleComponents X
      , (∀ {U : Over S} (φ : ofOver U ⟶ X),
            CompactSpace U.left → Etale φ →
              (irreducibleComponents U.left).Finite) ∧
          (codimZeroPoints X).Finite ∧
          ∀ x : Points X, localRingDimAt x = 0 → existsMonoFieldValuedPoint X x
      , ∃ X' : OpenSubspace X,
          IsScheme X'.X ∧ Dense X'.pointsSet ∧
            HasFiniteIrreducibleComponents X'.X ∧
            ∀ x' : Points X'.X, x' ∈ genericPoints X'.X →
              existsQuasiCompactFieldValuedPoint X (Points.map X'.ι x') ] :=
  sorry

namespace IsReasonable

/-- A decent algebraic space with finitely many irreducible components is
reasonable. -/
instance (priority := 900) of_isDecent_hasFiniteIrreducibleComponents {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] [HasFiniteIrreducibleComponents X] :
    IsReasonable X :=
  sorry

end IsReasonable

/-- The generic points of a dense open scheme with finitely many irreducible
components and quasi-compact generic-point morphisms map exactly onto the
generic points of the ambient algebraic space. -/
theorem genericPoints_eq_image_of_denseOpenScheme {S : Scheme.{u}}
    {X : AlgebraicSpace S} (X' : OpenSubspace X) (h_scheme : IsScheme X'.X)
    (h_dense : Dense X'.pointsSet) (h_fin : HasFiniteIrreducibleComponents X'.X)
    (h_qc : ∀ x' : Points X'.X, x' ∈ genericPoints X'.X →
      existsQuasiCompactFieldValuedPoint X (Points.map X'.ι x')) :
    Points.map X'.ι '' genericPoints X'.X = genericPoints X :=
  sorry

/-- Being decent with finitely many irreducible components is equivalent to every
quasi-compact scheme étale over `X` having finitely many irreducible components,
together with finitely many codimension-`0` points each represented by a
monomorphism `Spec(k) ⟶ X`. -/
theorem isDecent_hasFiniteIrreducibleComponents_iff_finiteEtaleSchemeComponents
    {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsDecent X ∧ HasFiniteIrreducibleComponents X ↔
      (∀ {U : Over S} (φ : ofOver U ⟶ X),
          CompactSpace U.left → Etale φ →
            (irreducibleComponents U.left).Finite) ∧
        (codimZeroPoints X).Finite ∧
        ∀ x : Points X, localRingDimAt x = 0 → existsMonoFieldValuedPoint X x :=
  (isDecent_finiteIrreducibleComponents_tfae X).out 0 1

/-- Being decent with finitely many irreducible components is equivalent to the
existence of a dense open schematic subspace with finitely many irreducible
components whose generic points give quasi-compact morphisms to `X`. -/
theorem isDecent_hasFiniteIrreducibleComponents_iff_existsDenseOpenScheme
    {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsDecent X ∧ HasFiniteIrreducibleComponents X ↔
      ∃ X' : OpenSubspace X,
        IsScheme X'.X ∧ Dense X'.pointsSet ∧
          HasFiniteIrreducibleComponents X'.X ∧
          ∀ x' : Points X'.X, x' ∈ genericPoints X'.X →
            existsQuasiCompactFieldValuedPoint X (Points.map X'.ι x') :=
  (isDecent_finiteIrreducibleComponents_tfae X).out 0 2

/-- Every quasi-compact scheme étale over `X` having finitely many irreducible
components, together with finitely many monomorphic codimension-`0` points, is
equivalent to the existence of a dense open schematic subspace with finitely
many irreducible components whose generic points give quasi-compact morphisms
to `X`. -/
theorem finiteEtaleSchemeComponents_iff_existsDenseOpenScheme
    {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ((∀ {U : Over S} (φ : ofOver U ⟶ X),
          CompactSpace U.left → Etale φ →
            (irreducibleComponents U.left).Finite) ∧
        (codimZeroPoints X).Finite ∧
        ∀ x : Points X, localRingDimAt x = 0 → existsMonoFieldValuedPoint X x) ↔
      ∃ X' : OpenSubspace X,
        IsScheme X'.X ∧ Dense X'.pointsSet ∧
          HasFiniteIrreducibleComponents X'.X ∧
          ∀ x' : Points X'.X, x' ∈ genericPoints X'.X →
            existsQuasiCompactFieldValuedPoint X (Points.map X'.ι x') :=
  (isDecent_finiteIrreducibleComponents_tfae X).out 1 2

end AlgebraicGeometry.AlgebraicSpace
