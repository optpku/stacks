/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import stacks_project.Chap65.Definition_65_12_5_ZariskiCover
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_8_4_Coproduct
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact

/-!
# Quasi-compact étale scheme coverings of algebraic spaces

This module records two covering conditions on an algebraic space: a Zariski
covering by quasi-compact surjective étale scheme charts, and an étale family of
schemes with quasi-compact self-fibre projections whose coproduct is surjective.
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

/-- A Zariski covering of `X` together with quasi-compact surjective étale
scheme charts of the open subspaces witnesses
`existsZariskiCoverQuasiCompactSurjectiveEtale`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} (𝒰 : ZariskiCover.{u, u} X)
    {U : 𝒰.I₀ → Over S} (φ : (i : 𝒰.I₀) → ofOver (U i) ⟶ 𝒰.X i)
    [∀ i, Etale (φ i)] [∀ i, Surjective (φ i)] [∀ i, QuasiCompact (φ i)] :
    existsZariskiCoverQuasiCompactSurjectiveEtale X :=
  sorry

/-- `existsZariskiCoverQuasiCompactSurjectiveEtale X` supplies a Zariski covering
of `X` and quasi-compact surjective étale scheme charts of the open subspaces. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : existsZariskiCoverQuasiCompactSurjectiveEtale X) :
    ∃ (𝒰 : ZariskiCover.{u, u} X) (U : 𝒰.I₀ → Over S)
      (φ : (i : 𝒰.I₀) → ofOver (U i) ⟶ 𝒰.X i),
      ∀ i, Etale (φ i) ∧ Surjective (φ i) ∧ QuasiCompact (φ i) :=
  sorry

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

/-- `existsEtaleCoverQuasiCompactSelfFibre X` unpacks to an étale family of
schemes covering `X` by a surjective coproduct morphism, with quasi-compact
self-fibre-product projections. -/
theorem existsEtaleCoverQuasiCompactSelfFibre_iff {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    existsEtaleCoverQuasiCompactSelfFibre X ↔
      ∃ (I : Type u) (U : I → Over S) (φ : (i : I) → ofOver (U i) ⟶ X),
        (∀ i, Etale (φ i)) ∧ Surjective (coproductDesc φ) ∧
          ∀ i, ∃ (R : Over S) (s t : R ⟶ U i),
            IsPullback (ofOverMap s) (ofOverMap t) (φ i) (φ i) ∧
              AlgebraicGeometry.QuasiCompact s.left ∧
                AlgebraicGeometry.QuasiCompact t.left :=
  sorry

namespace existsEtaleCoverQuasiCompactSelfFibre

/-- An étale family of schemes whose coproduct morphism is surjective and whose
self-fibre-product projections are quasi-compact witnesses
`existsEtaleCoverQuasiCompactSelfFibre`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type u}
    {U : I → Over S} (φ : (i : I) → ofOver (U i) ⟶ X) [∀ i, Etale (φ i)]
    (hsurj : Surjective (coproductDesc φ))
    (hqc : ∀ i, ∃ (R : Over S) (s t : R ⟶ U i),
      IsPullback (ofOverMap s) (ofOverMap t) (φ i) (φ i) ∧
        AlgebraicGeometry.QuasiCompact s.left ∧
          AlgebraicGeometry.QuasiCompact t.left) :
    existsEtaleCoverQuasiCompactSelfFibre X :=
  sorry

/-- `existsEtaleCoverQuasiCompactSelfFibre X` supplies an étale family of schemes
whose coproduct morphism is surjective and whose self-fibre-product projections
are quasi-compact. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : existsEtaleCoverQuasiCompactSelfFibre X) :
    ∃ (I : Type u) (U : I → Over S) (φ : (i : I) → ofOver (U i) ⟶ X),
      (∀ i, Etale (φ i)) ∧ Surjective (coproductDesc φ) ∧
        ∀ i, ∃ (R : Over S) (s t : R ⟶ U i),
          IsPullback (ofOverMap s) (ofOverMap t) (φ i) (φ i) ∧
            AlgebraicGeometry.QuasiCompact s.left ∧
              AlgebraicGeometry.QuasiCompact t.left :=
  sorry

end existsEtaleCoverQuasiCompactSelfFibre

end AlgebraicGeometry.AlgebraicSpace
