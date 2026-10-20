/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteComponents.Decent
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.20.4: Decency with finitely many irreducible components is
equivalent to the quasi-compact étale scheme condition with finitely many
monomorphic codimension-zero points, and to the existence of a dense open
scheme with finitely many components and quasi-compact generic-point morphisms.
These conditions imply reasonableness, and the generic points of such an open
map exactly onto the generic points of the ambient space. -/
@[stacks 0BB9] #check (AlgebraicGeometry.AlgebraicSpace.isDecent_finiteIrreducibleComponents_tfae :
    ∀ {S : Scheme.{u}}
    (X : AlgebraicSpace S),
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
              existsQuasiCompactFieldValuedPoint X (Points.map X'.ι x') ])

/- The equivalent conditions imply reasonableness. -/
@[stacks 0BB9] #check (AlgebraicGeometry.AlgebraicSpace.IsReasonable.of_isDecent_hasFiniteIrreducibleComponents :
    ∀ {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] [HasFiniteIrreducibleComponents X],
    IsReasonable X)

/- Generic points of a qualifying dense open scheme map onto the ambient generic points. -/
@[stacks 0BB9] #check (AlgebraicGeometry.AlgebraicSpace.genericPoints_eq_image_of_denseOpenScheme :
    ∀ {S : Scheme.{u}}
    {X : AlgebraicSpace S} (X' : OpenSubspace X) (h_scheme : IsScheme X'.X)
    (h_dense : Dense X'.pointsSet) (h_fin : HasFiniteIrreducibleComponents X'.X)
    (h_qc : ∀ x' : Points X'.X, x' ∈ genericPoints X'.X →
      existsQuasiCompactFieldValuedPoint X (Points.map X'.ι x')),
    Points.map X'.ι '' genericPoints X'.X = genericPoints X)

#check (AlgebraicGeometry.AlgebraicSpace.isDecent_hasFiniteIrreducibleComponents_iff_finiteEtaleSchemeComponents :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    IsDecent X ∧ HasFiniteIrreducibleComponents X ↔
      (∀ {U : Over S} (φ : ofOver U ⟶ X),
          CompactSpace U.left → Etale φ →
            (irreducibleComponents U.left).Finite) ∧
        (codimZeroPoints X).Finite ∧
        ∀ x : Points X, localRingDimAt x = 0 → existsMonoFieldValuedPoint X x)

#check (AlgebraicGeometry.AlgebraicSpace.isDecent_hasFiniteIrreducibleComponents_iff_existsDenseOpenScheme :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    IsDecent X ∧ HasFiniteIrreducibleComponents X ↔
      ∃ X' : OpenSubspace X,
        IsScheme X'.X ∧ Dense X'.pointsSet ∧
          HasFiniteIrreducibleComponents X'.X ∧
          ∀ x' : Points X'.X, x' ∈ genericPoints X'.X →
            existsQuasiCompactFieldValuedPoint X (Points.map X'.ι x'))

#check (AlgebraicGeometry.AlgebraicSpace.finiteEtaleSchemeComponents_iff_existsDenseOpenScheme :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    ((∀ {U : Over S} (φ : ofOver U ⟶ X),
          CompactSpace U.left → Etale φ →
            (irreducibleComponents U.left).Finite) ∧
        (codimZeroPoints X).Finite ∧
        ∀ x : Points X, localRingDimAt x = 0 → existsMonoFieldValuedPoint X x) ↔
      ∃ X' : OpenSubspace X,
        IsScheme X'.X ∧ Dense X'.pointsSet ∧
          HasFiniteIrreducibleComponents X'.X ∧
          ∀ x' : Points X'.X, x' ∈ genericPoints X'.X →
            existsQuasiCompactFieldValuedPoint X (Points.map X'.ι x'))

end AlgebraicGeometry.AlgebraicSpace
