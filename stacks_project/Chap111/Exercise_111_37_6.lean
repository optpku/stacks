/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.DegreeMul
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.DegreeMulExamples
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Veronese
import StacksCheckRecall

/-!
# Exercise 111.37.6: maps of `Proj`

A ring map `ψ : R → S` of `ℕ`-graded rings with `ψ(R_d) ⊆ S_{d e}` for `e ≥ 1`
induces a scheme morphism from the open `U = ⋃ D₊(ψ(f)) ⊆ Proj S` to `Proj R`.
-/

@[expose] public section

open CategoryTheory

universe u

/- Exercise 111.37.6 (1): the admissibility open consists of points for which some
positive homogeneous element maps outside the homogeneous prime ideal. -/
@[stacks 02A2] #check (AlgebraicGeometry.DegreeMulHom.mem_domain_iff :
  ∀ {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] {e : ℕ}
    (ψ : AlgebraicGeometry.DegreeMulHom 𝒜 ℬ e) (p : AlgebraicGeometry.Proj ℬ),
    p ∈ AlgebraicGeometry.DegreeMulHom.domain ψ ↔
      ∃ f : A, ∃ d : ℕ, 0 < d ∧ f ∈ 𝒜 d ∧ ψ.toRingHom f ∉ p.asHomogeneousIdeal)

/- Exercise 111.37.6 (2): the coordinate inclusion from `ℤ[X]` into `ℤ[X,Y]`
has a proper admissibility open. -/
@[stacks 02A2] #check (AlgebraicGeometry.coordinateRename_domain_ne_top :
  AlgebraicGeometry.DegreeMulHom.domain AlgebraicGeometry.coordinateRename ≠ ⊤)

/- Exercise 111.37.6 (3): the identity of standard-graded `ℤ[X,Y]` has full domain. -/
@[stacks 02A2] #check (AlgebraicGeometry.DegreeMulHom.id_domain_eq_top
  (MvPolynomial.standardGrading (Fin 2) ℤ) :
  AlgebraicGeometry.DegreeMulHom.domain
    (AlgebraicGeometry.DegreeMulHom.id (MvPolynomial.standardGrading (Fin 2) ℤ)) = ⊤)

/- Exercise 111.37.6 (4): the canonical continuous map comes with its sheaf map,
constructed by gluing the prescribed homogeneous-localization morphisms. -/
@[stacks 02A2] #check (AlgebraicGeometry.DegreeMulHom.map :
  ∀ {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] {e : ℕ}
    (ψ : AlgebraicGeometry.DegreeMulHom 𝒜 ℬ e),
    (AlgebraicGeometry.DegreeMulHom.domain ψ).toScheme ⟶ AlgebraicGeometry.Proj 𝒜)

/- Exercise 111.37.6 (5): every positive Veronese inclusion has full domain,
and its constructed morphism of projective spectra is an isomorphism. -/
@[stacks 02A2] #check (AlgebraicGeometry.ofInclusion_isIso :
  ∀ {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (e : ℕ) (he : 1 ≤ e),
    IsIso (AlgebraicGeometry.DegreeMulHom.mapOnTarget
      (AlgebraicGeometry.DegreeMulHom.ofInclusion 𝒜 e he)
      (AlgebraicGeometry.ofInclusion_domain_eq_top 𝒜 e he)))
