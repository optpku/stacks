/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-!
# Étale-local characterizations of derived quasi-coherence

Membership of an object of `D(𝒪_X)` in `D_QCoh(𝒪_X)` is tested after étale derived
pullback from affine schemes, from schemes, and from algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace


namespace DerivedQCoh

/-- For every étale morphism `φ : U ⟶ X` from an affine scheme, the derived pullback of
`E` lies in `D_QCoh(𝒪_U)`. -/
def forallAffine {S : Scheme.{u}} {X : AlgebraicSpace S} (E : ModuleDerived X) : Prop :=
  ∀ (U : Over S) [IsAffine U.left] (φ : ofOver U ⟶ X) [Etale φ],
    derivedQuasiCoherentModuleProperty (ofOver U) ((ModuleDerived.pullback φ).obj E)

/-- `forallAffine E` is the universal affine étale derived quasi-coherence condition. -/
theorem forallAffine_def {S : Scheme.{u}} {X : AlgebraicSpace S} (E : ModuleDerived X) :
    forallAffine E ↔
      ∀ (U : Over S) [IsAffine U.left] (φ : ofOver U ⟶ X) [Etale φ],
        derivedQuasiCoherentModuleProperty (ofOver U)
          ((ModuleDerived.pullback φ).obj E) :=
  Iff.rfl

namespace forallAffine

/-- The universal affine étale derived quasi-coherence condition witnesses
`forallAffine E`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {E : ModuleDerived X}
    (h : ∀ (U : Over S) [IsAffine U.left] (φ : ofOver U ⟶ X) [Etale φ],
      derivedQuasiCoherentModuleProperty (ofOver U)
        ((ModuleDerived.pullback φ).obj E)) : forallAffine E :=
  h

/-- An object satisfying `forallAffine E` has derived-quasi-coherent pullback along every
étale morphism from an affine scheme. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {E : ModuleDerived X}
    (h : forallAffine E) :
    ∀ (U : Over S) [IsAffine U.left] (φ : ofOver U ⟶ X) [Etale φ],
      derivedQuasiCoherentModuleProperty (ofOver U)
        ((ModuleDerived.pullback φ).obj E) :=
  h

/-- Derived pullback along a given étale morphism from an affine scheme lies in
`D_QCoh`. -/
theorem apply {S : Scheme.{u}} {X : AlgebraicSpace S} {E : ModuleDerived X}
    (h : forallAffine E) {U : Over S} [IsAffine U.left] (φ : ofOver U ⟶ X)
    [Etale φ] :
    derivedQuasiCoherentModuleProperty (ofOver U)
      ((ModuleDerived.pullback φ).obj E) :=
  h U φ

end forallAffine

/-- For every étale morphism `φ : U ⟶ X` from a scheme, the derived pullback of `E`
lies in `D_QCoh(𝒪_U)`. -/
def forallScheme {S : Scheme.{u}} {X : AlgebraicSpace S} (E : ModuleDerived X) : Prop :=
  ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ],
    derivedQuasiCoherentModuleProperty (ofOver U) ((ModuleDerived.pullback φ).obj E)

/-- `forallScheme E` is the universal scheme étale derived quasi-coherence condition. -/
theorem forallScheme_def {S : Scheme.{u}} {X : AlgebraicSpace S} (E : ModuleDerived X) :
    forallScheme E ↔
      ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ],
        derivedQuasiCoherentModuleProperty (ofOver U)
          ((ModuleDerived.pullback φ).obj E) :=
  Iff.rfl

namespace forallScheme

/-- The universal scheme étale derived quasi-coherence condition witnesses
`forallScheme E`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {E : ModuleDerived X}
    (h : ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ],
      derivedQuasiCoherentModuleProperty (ofOver U)
        ((ModuleDerived.pullback φ).obj E)) : forallScheme E :=
  h

/-- An object satisfying `forallScheme E` has derived-quasi-coherent pullback along every
étale morphism from a scheme. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {E : ModuleDerived X}
    (h : forallScheme E) :
    ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ],
      derivedQuasiCoherentModuleProperty (ofOver U)
        ((ModuleDerived.pullback φ).obj E) :=
  h

/-- Derived pullback along a given étale morphism from a scheme lies in `D_QCoh`. -/
theorem apply {S : Scheme.{u}} {X : AlgebraicSpace S} {E : ModuleDerived X}
    (h : forallScheme E) {U : Over S} (φ : ofOver U ⟶ X) [Etale φ] :
    derivedQuasiCoherentModuleProperty (ofOver U)
      ((ModuleDerived.pullback φ).obj E) :=
  h U φ

end forallScheme

/-- There exists a scheme `U` over `S` and a surjective étale morphism `φ : U ⟶ X` such
that the derived pullback of `E` lies in `D_QCoh(𝒪_U)`. -/
def existsScheme {S : Scheme.{u}} {X : AlgebraicSpace S} (E : ModuleDerived X) : Prop :=
  ∃ (U : Over S) (φ : ofOver U ⟶ X) (hφ : Etale φ) (_ : Surjective φ),
    derivedQuasiCoherentModuleProperty (ofOver U)
      ((ModuleDerived.pullback φ).obj E)

/-- `existsScheme E` is the existence of a surjective étale scheme atlas along which the
derived pullback of `E` lies in `D_QCoh`. -/
theorem existsScheme_def {S : Scheme.{u}} {X : AlgebraicSpace S} (E : ModuleDerived X) :
    existsScheme E ↔
      ∃ (U : Over S) (φ : ofOver U ⟶ X) (hφ : Etale φ) (_ : Surjective φ),
        derivedQuasiCoherentModuleProperty (ofOver U)
          ((ModuleDerived.pullback φ).obj E) :=
  Iff.rfl

namespace existsScheme

/-- A surjective étale scheme atlas along which the derived pullback of `E` lies in
`D_QCoh` witnesses `existsScheme E`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {E : ModuleDerived X} {U : Over S}
    (φ : ofOver U ⟶ X) [Etale φ] [Surjective φ]
    (hE : derivedQuasiCoherentModuleProperty (ofOver U)
      ((ModuleDerived.pullback φ).obj E)) : existsScheme E :=
  ⟨U, φ, inferInstance, inferInstance, hE⟩

/-- An object satisfying `existsScheme E` admits a surjective étale scheme atlas along
which its derived pullback lies in `D_QCoh`. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {E : ModuleDerived X}
    (h : existsScheme E) :
    ∃ (U : Over S) (φ : ofOver U ⟶ X) (hφ : Etale φ) (_ : Surjective φ),
      derivedQuasiCoherentModuleProperty (ofOver U)
        ((ModuleDerived.pullback φ).obj E) :=
  h

end existsScheme

/-- There exists a surjective étale morphism of algebraic spaces `f : Y ⟶ X` such that
the derived pullback of `E` lies in `D_QCoh(𝒪_Y)`. -/
def existsEtale {S : Scheme.{u}} {X : AlgebraicSpace S} (E : ModuleDerived X) : Prop :=
  ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X) (hf : Etale f) (_ : Surjective f),
    derivedQuasiCoherentModuleProperty Y ((ModuleDerived.pullback f).obj E)

/-- `existsEtale E` is the existence of a surjective étale algebraic-space cover along
which the derived pullback of `E` lies in `D_QCoh`. -/
theorem existsEtale_def {S : Scheme.{u}} {X : AlgebraicSpace S} (E : ModuleDerived X) :
    existsEtale E ↔
      ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X) (hf : Etale f) (_ : Surjective f),
        derivedQuasiCoherentModuleProperty Y
          ((ModuleDerived.pullback f).obj E) :=
  Iff.rfl

namespace existsEtale

/-- A surjective étale morphism of algebraic spaces along which the derived pullback of
`E` lies in `D_QCoh` witnesses `existsEtale E`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {E : ModuleDerived X}
    {Y : AlgebraicSpace S} (f : Y ⟶ X) [Etale f] [Surjective f]
    (hE : derivedQuasiCoherentModuleProperty Y
      ((ModuleDerived.pullback f).obj E)) : existsEtale E :=
  ⟨Y, f, inferInstance, inferInstance, hE⟩

/-- An object satisfying `existsEtale E` admits a surjective étale algebraic-space cover
along which its derived pullback lies in `D_QCoh`. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {E : ModuleDerived X}
    (h : existsEtale E) :
    ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X) (hf : Etale f) (_ : Surjective f),
      derivedQuasiCoherentModuleProperty Y
        ((ModuleDerived.pullback f).obj E) :=
  h

end existsEtale

/-- Quasi-coherence of every cohomology sheaf is equivalent to étale-local testing
on all affine schemes, on all schemes, on one surjective scheme cover, or on one
surjective algebraic-space cover. -/
theorem tfae {S : Scheme.{u}} {X : AlgebraicSpace S} (E : ModuleDerived X) :
    List.TFAE [derivedQuasiCoherentModuleProperty X E, forallAffine E, forallScheme E,
      existsScheme E, existsEtale E] :=
  sorry

/-- Membership of `E` in `D_QCoh(𝒪_X)` is equivalent to derived quasi-coherence of its
pullback along every étale morphism from an affine scheme. -/
theorem iff_forallAffine {S : Scheme.{u}} {X : AlgebraicSpace S} (E : ModuleDerived X) :
    derivedQuasiCoherentModuleProperty X E ↔ forallAffine E :=
  (tfae E).out 0 1

/-- Membership of `E` in `D_QCoh(𝒪_X)` is equivalent to derived quasi-coherence of its
pullback along every étale morphism from a scheme. -/
theorem iff_forallScheme {S : Scheme.{u}} {X : AlgebraicSpace S} (E : ModuleDerived X) :
    derivedQuasiCoherentModuleProperty X E ↔ forallScheme E :=
  (tfae E).out 0 2

/-- Membership of `E` in `D_QCoh(𝒪_X)` is equivalent to the existence of a surjective
étale scheme atlas along which the derived pullback of `E` lies in `D_QCoh`. -/
theorem iff_existsScheme {S : Scheme.{u}} {X : AlgebraicSpace S} (E : ModuleDerived X) :
    derivedQuasiCoherentModuleProperty X E ↔ existsScheme E :=
  (tfae E).out 0 3

/-- Membership of `E` in `D_QCoh(𝒪_X)` is equivalent to the existence of a surjective
étale algebraic-space cover along which the derived pullback of `E` lies in `D_QCoh`. -/
theorem iff_existsEtale {S : Scheme.{u}} {X : AlgebraicSpace S} (E : ModuleDerived X) :
    derivedQuasiCoherentModuleProperty X E ↔ existsEtale E :=
  (tfae E).out 0 4

end DerivedQCoh

end AlgebraicGeometry.AlgebraicSpace
