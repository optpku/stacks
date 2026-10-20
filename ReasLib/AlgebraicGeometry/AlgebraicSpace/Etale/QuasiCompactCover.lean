/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Coproduct
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact

/-!
# Quasi-compact étale scheme coverings of algebraic spaces

A Zariski covering by quasi-compact surjective étale scheme charts exists if and
only if there is an étale family of schemes with quasi-compact self-fibre
projections whose coproduct is surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- There is a Zariski covering of `X` by open subspaces each admitting a
quasi-compact surjective étale morphism from a scheme. -/
def existsZariskiCoverQuasiCompactSurjectiveEtale {S : Scheme.{u}}
    (X : AlgebraicSpace S) : Prop :=
  ∃ (𝒰 : ZariskiCover.{u, u} X) (U : 𝒰.I₀ → Over S)
    (φ : (i : 𝒰.I₀) → ofOver (U i) ⟶ 𝒰.X i),
    ∀ i, Etale (φ i) ∧ Surjective (φ i) ∧ QuasiCompact (φ i)

namespace existsZariskiCoverQuasiCompactSurjectiveEtale

/-- A Zariski covering with quasi-compact surjective étale scheme charts
satisfies the corresponding covering condition. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} (𝒰 : ZariskiCover.{u, u} X)
    {U : 𝒰.I₀ → Over S} (φ : (i : 𝒰.I₀) → ofOver (U i) ⟶ 𝒰.X i)
    [∀ i, Etale (φ i)] [∀ i, Surjective (φ i)] [∀ i, QuasiCompact (φ i)] :
    existsZariskiCoverQuasiCompactSurjectiveEtale X :=
  ⟨𝒰, U, φ, fun i ↦ ⟨inferInstance, inferInstance, inferInstance⟩⟩

/-- The Zariski covering condition supplies a covering and quasi-compact
surjective étale scheme charts of its open subspaces. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : existsZariskiCoverQuasiCompactSurjectiveEtale X) :
    ∃ (𝒰 : ZariskiCover.{u, u} X) (U : 𝒰.I₀ → Over S)
      (φ : (i : 𝒰.I₀) → ofOver (U i) ⟶ 𝒰.X i),
      ∀ i, Etale (φ i) ∧ Surjective (φ i) ∧ QuasiCompact (φ i) :=
  h

end existsZariskiCoverQuasiCompactSurjectiveEtale

/-- There is an étale family of schemes over `X` whose coproduct morphism is
surjective and whose self-fibre-product projections are quasi-compact. -/
def existsEtaleCoverQuasiCompactSelfFibre {S : Scheme.{u}}
    (X : AlgebraicSpace S) : Prop :=
  ∃ (I : Type u) (U : I → Over S) (φ : (i : I) → ofOver (U i) ⟶ X),
    (∀ i, Etale (φ i)) ∧ Surjective (coproductDesc φ) ∧
      ∀ i, ∃ (R : Over S) (s t : R ⟶ U i),
        IsPullback (ofOverMap s) (ofOverMap t) (φ i) (φ i) ∧
          AlgebraicGeometry.QuasiCompact s.left ∧
            AlgebraicGeometry.QuasiCompact t.left

/-- The étale covering condition is equivalent to the existence of a family
with surjective coproduct and quasi-compact self-fibre-product projections. -/
theorem existsEtaleCoverQuasiCompactSelfFibre_iff {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    existsEtaleCoverQuasiCompactSelfFibre X ↔
      ∃ (I : Type u) (U : I → Over S) (φ : (i : I) → ofOver (U i) ⟶ X),
        (∀ i, Etale (φ i)) ∧ Surjective (coproductDesc φ) ∧
          ∀ i, ∃ (R : Over S) (s t : R ⟶ U i),
            IsPullback (ofOverMap s) (ofOverMap t) (φ i) (φ i) ∧
              AlgebraicGeometry.QuasiCompact s.left ∧
                AlgebraicGeometry.QuasiCompact t.left :=
  Iff.rfl

namespace existsEtaleCoverQuasiCompactSelfFibre

/-- An étale family with surjective coproduct and quasi-compact
self-fibre-product projections satisfies the corresponding covering condition. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type u}
    {U : I → Over S} (φ : (i : I) → ofOver (U i) ⟶ X) [∀ i, Etale (φ i)]
    (hsurj : Surjective (coproductDesc φ))
    (hqc : ∀ i, ∃ (R : Over S) (s t : R ⟶ U i),
      IsPullback (ofOverMap s) (ofOverMap t) (φ i) (φ i) ∧
        AlgebraicGeometry.QuasiCompact s.left ∧
          AlgebraicGeometry.QuasiCompact t.left) :
    existsEtaleCoverQuasiCompactSelfFibre X :=
  ⟨I, U, φ, fun i ↦ inferInstance, hsurj, hqc⟩

/-- The étale covering condition supplies a family with surjective coproduct
and quasi-compact self-fibre-product projections. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : existsEtaleCoverQuasiCompactSelfFibre X) :
    ∃ (I : Type u) (U : I → Over S) (φ : (i : I) → ofOver (U i) ⟶ X),
      (∀ i, Etale (φ i)) ∧ Surjective (coproductDesc φ) ∧
        ∀ i, ∃ (R : Over S) (s t : R ⟶ U i),
          IsPullback (ofOverMap s) (ofOverMap t) (φ i) (φ i) ∧
            AlgebraicGeometry.QuasiCompact s.left ∧
              AlgebraicGeometry.QuasiCompact t.left :=
  h

end existsEtaleCoverQuasiCompactSelfFibre

/-- An algebraic space admits a Zariski covering by quasi-compact surjective
étale scheme charts if and only if it admits an étale scheme covering with
quasi-compact self-fibre-product projections. -/
theorem existsZariskiCoverQuasiCompactSurjectiveEtale_iff {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    existsZariskiCoverQuasiCompactSurjectiveEtale X ↔
      existsEtaleCoverQuasiCompactSelfFibre X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
