/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian.EtaleChart
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.SchemeEtaleComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Locality
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.EtaleComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-! # Dualizing complexes on étale scheme charts

A derived module on a scheme chart is dualizing when its image on the small étale
site is isomorphic to the canonical pullback of a Zariski dualizing complex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.Scheme.DerivedQCoh (SmallEtale epsilonStar)
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace DerivedQCoh

/-- The restriction of `K` to an étale scheme chart `U` is a dualizing complex for `U`
when it is isomorphic on the small étale site to `ε*` of a Zariski dualizing complex. -/
def isDualizingOnScheme {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsLocallyNoetherian U.left]
    (K : ModuleDerived (ofOver U)) : Prop :=
  ∃ ω : Scheme.DerivedQCoh U.left,
    Scheme.IsDualizingComplex ω.obj ∧
      IsIsomorphic ((toEtaleDerived U).obj K)
        ((SmallEtale.inclusion U.left).obj
          ((epsilonStar U.left).obj ω))

/-- Dualizingness on an étale scheme chart is the existence of a Zariski dualizing
complex whose `ε*` recovers the chart restriction in `D(𝒪_étale)`. -/
theorem isDualizingOnScheme_iff {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsLocallyNoetherian U.left]
    (K : ModuleDerived (ofOver U)) :
    isDualizingOnScheme U K ↔
      ∃ ω : Scheme.DerivedQCoh U.left,
        Scheme.IsDualizingComplex ω.obj ∧
          IsIsomorphic ((toEtaleDerived U).obj K)
            ((SmallEtale.inclusion U.left).obj
              ((epsilonStar U.left).obj ω)) :=
  Iff.rfl

namespace isDualizingOnScheme

/-- A Zariski dualizing complex whose `ε*` is isomorphic to the chart restriction
witnesses dualizingness on that scheme chart. -/
theorem of {S : Scheme.{u}} {U : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian U.left]
    {K : ModuleDerived (ofOver U)} (ω : Scheme.DerivedQCoh U.left)
    (hω : Scheme.IsDualizingComplex ω.obj)
    (hiso : IsIsomorphic ((toEtaleDerived U).obj K)
      ((SmallEtale.inclusion U.left).obj
        ((epsilonStar U.left).obj ω))) :
    isDualizingOnScheme U K :=
  ⟨ω, hω, hiso⟩

/-- Dualizingness on a scheme chart yields a Zariski dualizing complex whose `ε*`
recovers the chart restriction. -/
theorem spec {S : Scheme.{u}} {U : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian U.left]
    {K : ModuleDerived (ofOver U)} (h : isDualizingOnScheme U K) :
    ∃ ω : Scheme.DerivedQCoh U.left,
      Scheme.IsDualizingComplex ω.obj ∧
        IsIsomorphic ((toEtaleDerived U).obj K)
          ((SmallEtale.inclusion U.left).obj
            ((epsilonStar U.left).obj ω)) :=
  h

end isDualizingOnScheme

/-- For every étale morphism `φ : U ⟶ X` from a locally Noetherian scheme, the
restriction of `K` is a dualizing complex for `U`. -/
def forallEtaleScheme {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (K : DerivedQCoh X) : Prop :=
  ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ]
    [AlgebraicGeometry.IsLocallyNoetherian U.left],
    isDualizingOnScheme U ((ModuleDerived.pullback φ).obj ((inclusion X).obj K))

/-- `forallEtaleScheme K` is dualizingness of the restriction of `K` along every étale
scheme chart. -/
theorem forallEtaleScheme_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (K : DerivedQCoh X) :
    forallEtaleScheme K ↔
      ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ]
        [AlgebraicGeometry.IsLocallyNoetherian U.left],
        isDualizingOnScheme U
          ((ModuleDerived.pullback φ).obj ((inclusion X).obj K)) :=
  Iff.rfl

namespace forallEtaleScheme

/-- Dualizingness of the restriction of `K` along every étale scheme chart witnesses
`forallEtaleScheme K`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    {K : DerivedQCoh X}
    (h : ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ]
      [AlgebraicGeometry.IsLocallyNoetherian U.left],
      isDualizingOnScheme U
        ((ModuleDerived.pullback φ).obj ((inclusion X).obj K))) :
    forallEtaleScheme K :=
  h

/-- An object satisfying `forallEtaleScheme K` has dualizing restriction along every
étale scheme chart. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    {K : DerivedQCoh X} (h : forallEtaleScheme K) :
    ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ]
      [AlgebraicGeometry.IsLocallyNoetherian U.left],
      isDualizingOnScheme U
        ((ModuleDerived.pullback φ).obj ((inclusion X).obj K)) :=
  h

/-- Restriction of `K` along a given étale scheme chart is dualizing. -/
theorem apply {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    {K : DerivedQCoh X} (h : forallEtaleScheme K) {U : Over S}
    (φ : ofOver U ⟶ X) [Etale φ]
    [AlgebraicGeometry.IsLocallyNoetherian U.left] :
    isDualizingOnScheme U
      ((ModuleDerived.pullback φ).obj ((inclusion X).obj K)) :=
  h U φ

end forallEtaleScheme

/-- There exists a surjective étale morphism `φ : U ⟶ X` from a locally Noetherian
scheme such that the restriction of `K` is a dualizing complex for `U`. -/
def existsSurjectiveEtaleScheme {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (K : DerivedQCoh X) : Prop :=
  ∃ (U : Over S) (φ : ofOver U ⟶ X) (hφ : Etale φ) (_ : Surjective φ)
    (_ : AlgebraicGeometry.IsLocallyNoetherian U.left),
    isDualizingOnScheme U
      ((ModuleDerived.pullback φ).obj ((inclusion X).obj K))

/-- `existsSurjectiveEtaleScheme K` is the existence of a surjective étale scheme chart
along which the restriction of `K` is dualizing. -/
theorem existsSurjectiveEtaleScheme_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (K : DerivedQCoh X) :
    existsSurjectiveEtaleScheme K ↔
      ∃ (U : Over S) (φ : ofOver U ⟶ X) (hφ : Etale φ) (_ : Surjective φ)
        (_ : AlgebraicGeometry.IsLocallyNoetherian U.left),
        isDualizingOnScheme U
          ((ModuleDerived.pullback φ).obj ((inclusion X).obj K)) :=
  Iff.rfl

namespace existsSurjectiveEtaleScheme

/-- A surjective étale scheme chart along which the restriction of `K` is dualizing
witnesses `existsSurjectiveEtaleScheme K`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    {K : DerivedQCoh X} {U : Over S} (φ : ofOver U ⟶ X) [Etale φ] [Surjective φ]
    [AlgebraicGeometry.IsLocallyNoetherian U.left]
    (hK : isDualizingOnScheme U
      ((ModuleDerived.pullback φ).obj ((inclusion X).obj K))) :
    existsSurjectiveEtaleScheme K :=
  ⟨U, φ, inferInstance, inferInstance, inferInstance, hK⟩

/-- An object satisfying `existsSurjectiveEtaleScheme K` admits a surjective étale
scheme chart along which its restriction is dualizing. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    {K : DerivedQCoh X} (h : existsSurjectiveEtaleScheme K) :
    ∃ (U : Over S) (φ : ofOver U ⟶ X) (hφ : Etale φ) (_ : Surjective φ)
      (_ : AlgebraicGeometry.IsLocallyNoetherian U.left),
      isDualizingOnScheme U
        ((ModuleDerived.pullback φ).obj ((inclusion X).obj K)) :=
  h

end existsSurjectiveEtaleScheme

/-- For a locally Noetherian algebraic space, a derived quasi-coherent complex has
dualizing restriction to every étale scheme chart if and only if it has dualizing
restriction to one surjective étale scheme chart. -/
theorem isDualizingOnScheme_forall_iff_exists {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsLocallyNoetherian X] (K : DerivedQCoh X) :
    forallEtaleScheme K ↔ existsSurjectiveEtaleScheme K :=
  sorry

end DerivedQCoh

end AlgebraicGeometry.AlgebraicSpace
