/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocal
public import ReasLib.AlgebraicGeometry.Scheme.Jacobson.Etale

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
  exists_jacobson_etaleCover (X := X)

/-- A representable étale locally-surjective atlas from a Jacobson scheme witnesses that the
algebraic space is Jacobson. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : existsSurjectiveEtale (fun U : Scheme.{u} ↦ JacobsonSpace U) X) :
    IsJacobson X :=
  ⟨h⟩

/-- An algebraic space is Jacobson if and only if every étale morphism from a scheme has
Jacobson source. -/
theorem iff_forallEtale {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsJacobson X ↔ forallEtale (fun U : Scheme.{u} ↦ JacobsonSpace U) X :=
  Iff.trans ⟨fun h ↦ h.exists_jacobson_etaleCover, fun h ↦ ⟨h⟩⟩
    (existsSurjectiveEtale_iff_forallEtale (fun U : Scheme.{u} ↦ JacobsonSpace U) X)

/-- An étale morphism from a scheme into a Jacobson algebraic space has Jacobson source. -/
theorem jacobsonSpace_etale {S : Scheme.{u}} {X : AlgebraicSpace S} [IsJacobson X]
    {U : Over S} (φ : ofOver U ⟶ X)
    (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ) :
    JacobsonSpace U.left :=
  forallEtale.apply ((iff_forallEtale X).mp inferInstance) φ hφ

end IsJacobson

/-- A Jacobson scheme over `S`, viewed as an algebraic space, is Jacobson. -/
instance instIsJacobson_ofOver {S : Scheme.{u}} (T : Over S) [JacobsonSpace T.left] :
    IsJacobson (ofOver T) :=
  ⟨(existsSurjectiveEtale_ofOver (fun U : Scheme.{u} ↦ JacobsonSpace U) T).mpr
    inferInstance⟩

end AlgebraicGeometry.AlgebraicSpace
