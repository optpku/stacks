module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap67.Lemma_67_49_1_FiniteComponents
public import stacks_project.Chap68.Definition_68_22_1_GenericPoints
public import stacks_project.Chap68.Lemma_68_4_5_Fibre
public import stacks_project.Chap68.Lemma_68_17_4_Relative

/-!
# Finitely many irreducible components of an algebraic space

For an algebraic space, being decent with finitely many irreducible components
is equivalent to a finite-étale-scheme test at codimension-zero points and to
the existence of a dense open schematic subspace with quasi-compact generic
points. Either condition implies that the space is reasonable.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.20.4 (1): Let `S` be a scheme. Let `X` be an algebraic space over `S`.
The following are equivalent: `X` is decent and `|X|` has finitely many
irreducible components; every quasi-compact scheme étale over `X` has finitely
many irreducible components, there are finitely many points of `|X|` of
codimension `0` on `X`, and each of these can be represented by a monomorphism
`Spec(k) ⟶ X`; there exists a dense open subspace `X' ⊂ X` which is a scheme,
`X'` has finitely many irreducible components, and each generic point of `X'`
gives a quasi-compact morphism to `X`.

Here a quasi-compact scheme is `CompactSpace U.left`, étale means `Etale φ`,
finitely many irreducible components of a scheme means
`(irreducibleComponents U.left).Finite`, finitely many irreducible components of
an algebraic space means `HasFiniteIrreducibleComponents`, codimension `0`
means `localRingDimAt x = 0`, representation by a monomorphism `Spec(k) ⟶ X` is
`existsMonoFieldValuedPoint X x`, a dense open scheme is an `OpenSubspace` `X'`
with `IsScheme X'.X` and `Dense X'.pointsSet`, and `x' ⟶ X` quasi-compact is
`existsQuasiCompactFieldValuedPoint X (Points.map X'.ι x')`. -/
@[stacks 0BB9]
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

/-- Lemma 68.20.4 (2): Let `S` be a scheme. Let `X` be an algebraic space over `S`.
If `X` is decent and `|X|` has finitely many irreducible components, then `X` is
reasonable. -/
@[stacks 0BB9]
theorem of_isDecent_hasFiniteIrreducibleComponents {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] [HasFiniteIrreducibleComponents X] :
    IsReasonable X :=
  sorry

end IsReasonable

/-- Lemma 68.20.4 (3): Let `S` be a scheme. Let `X` be an algebraic space over `S`.
If `X' ⊂ X` is a dense open subspace which is a scheme, `X'` has finitely many
irreducible components, and each generic point of `X'` gives a quasi-compact
morphism to `X`, then the images of those generic points are exactly the generic
points of the irreducible components of `|X|`. -/
@[stacks 0BB9]
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
  sorry

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
  sorry

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
  sorry

end AlgebraicGeometry.AlgebraicSpace
