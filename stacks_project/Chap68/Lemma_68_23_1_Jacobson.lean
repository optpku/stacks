/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.JacobsonSpace
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Lemma_66_7_1
public import stacks_project.Chap66.Lemma_66_7_1_EtaleLocal
public import stacks_project.Chap66.Remark_66_7_3_EtaleLocal

/-!
# Jacobson algebraic spaces

An algebraic space is Jacobson when it admits a representable étale locally-surjective
atlas from a Jacobson scheme, equivalently when every étale morphism from a scheme has
Jacobson source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space is Jacobson if it admits a representable étale locally-surjective
atlas whose source is a Jacobson scheme. -/
@[mk_iff]
class IsJacobson {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- There is a representable étale locally-surjective atlas from a Jacobson scheme. -/
  exists_jacobson_etaleCover :
    existsSurjectiveEtale (fun U : Scheme.{u} ↦ JacobsonSpace U) X

namespace IsJacobson

/-- A Jacobson algebraic space admits a representable étale locally-surjective atlas from a
Jacobson scheme. -/
theorem spec {S : Scheme.{u}} (X : AlgebraicSpace S) [IsJacobson X] :
    existsSurjectiveEtale (fun U : Scheme.{u} ↦ JacobsonSpace U) X :=
  sorry

/-- A representable étale locally-surjective atlas from a Jacobson scheme witnesses that the
algebraic space is Jacobson. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : existsSurjectiveEtale (fun U : Scheme.{u} ↦ JacobsonSpace U) X) :
    IsJacobson X :=
  sorry

/-- An algebraic space is Jacobson if and only if every étale morphism from a scheme has
Jacobson source. -/
theorem iff_forallEtale {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsJacobson X ↔ forallEtale (fun U : Scheme.{u} ↦ JacobsonSpace U) X :=
  sorry

/-- An étale morphism from a scheme into a Jacobson algebraic space has Jacobson source. -/
theorem jacobsonSpace_etale {S : Scheme.{u}} {X : AlgebraicSpace S} [IsJacobson X]
    {U : Over S} (φ : ofOver U ⟶ X)
    (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ) :
    JacobsonSpace U.left :=
  sorry

end IsJacobson

/-- A Jacobson scheme over `S`, viewed as an algebraic space, is Jacobson. -/
instance instIsJacobson_ofOver {S : Scheme.{u}} (T : Over S) [JacobsonSpace T.left] :
    IsJacobson (ofOver T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
