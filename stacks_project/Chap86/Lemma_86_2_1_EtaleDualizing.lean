/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Locality
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Proposition_66_32_1_Comparison
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap75.Lemma_75_4_2_Pullback
public import stacks_project.Chap75.Lemma_75_5_2_EtaleLocal

/-!
# Dualizing complexes on étale scheme charts

Restriction of `K ∈ D_QCoh(𝒪_X)` along an étale morphism `U ⟶ X` from a scheme is
dualizing for `U` when it is isomorphic, on the small étale site of `U`, to `ε*` of a
Zariski dualizing complex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.Scheme.DerivedQCoh (SmallEtale epsilonStar)
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Pushforward of modules along `schemeEtaleRingedHom U` preserves finite limits. -/
instance schemeEtaleRingedHom_modulePushforward_preservesFiniteLimits
    {S : Scheme.{u}} (U : Over S) :
    PreservesFiniteLimits (schemeEtaleRingedHom U).modulePushforward.{u} :=
  sorry

/-- Pushforward of modules along `schemeEtaleRingedHom U` preserves finite colimits. -/
instance schemeEtaleRingedHom_modulePushforward_preservesFiniteColimits
    {S : Scheme.{u}} (U : Over S) :
    PreservesFiniteColimits (schemeEtaleRingedHom U).modulePushforward.{u} :=
  sorry

namespace DerivedQCoh

/-- Derived comparison identifying `D(𝒪_{ofOver U})` with `D(𝒪_étale)` of the underlying
scheme of `U`. -/
def toEtaleDerived {S : Scheme.{u}} (U : Over S) :
    ModuleDerived (ofOver U) ⥤
      DerivedCategory (RingedSite.ModuleCat.{u} (Scheme.Etale.Small.ringedSite U.left)) :=
  (schemeEtaleRingedHom U).modulePushforward.{u}.mapDerivedCategory

/-- `toEtaleDerived U` is exact derived pushforward along `schemeEtaleRingedHom U`. -/
theorem toEtaleDerived_eq {S : Scheme.{u}} (U : Over S) :
    toEtaleDerived U =
      (schemeEtaleRingedHom U).modulePushforward.{u}.mapDerivedCategory :=
  sorry

/-- Objectwise, `toEtaleDerived` is exact derived pushforward along
`schemeEtaleRingedHom U`. -/
theorem toEtaleDerived_obj {S : Scheme.{u}} (U : Over S)
    (K : ModuleDerived (ofOver U)) :
    (toEtaleDerived U).obj K =
      ((schemeEtaleRingedHom U).modulePushforward.{u}.mapDerivedCategory).obj K :=
  sorry

/-- An étale scheme chart of a locally Noetherian algebraic space has locally Noetherian
underlying scheme. -/
theorem isLocallyNoetherian_left_of_etaleChart {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsLocallyNoetherian X] {U : Over S}
    (φ : ofOver U ⟶ X) [Etale φ] :
    AlgebraicGeometry.IsLocallyNoetherian U.left :=
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- An object satisfying `forallEtaleScheme K` has dualizing restriction along every
étale scheme chart. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    {K : DerivedQCoh X} (h : forallEtaleScheme K) :
    ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ]
      [AlgebraicGeometry.IsLocallyNoetherian U.left],
      isDualizingOnScheme U
        ((ModuleDerived.pullback φ).obj ((inclusion X).obj K)) :=
  sorry

/-- Restriction of `K` along a given étale scheme chart is dualizing. -/
theorem apply {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    {K : DerivedQCoh X} (h : forallEtaleScheme K) {U : Over S}
    (φ : ofOver U ⟶ X) [Etale φ]
    [AlgebraicGeometry.IsLocallyNoetherian U.left] :
    isDualizingOnScheme U
      ((ModuleDerived.pullback φ).obj ((inclusion X).obj K)) :=
  sorry

end forallEtaleScheme

/-- There exists a surjective étale morphism `φ : U ⟶ X` from a locally Noetherian
scheme such that the restriction of `K` is a dualizing complex for `U`. -/
def existsSurjectiveEtaleScheme {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (K : DerivedQCoh X) : Prop :=
  ∃ (U : Over S) (φ : ofOver U ⟶ X) (hφ : Etale φ) (_ : Surjective φ)
    (_ : AlgebraicGeometry.IsLocallyNoetherian U.left),
    isDualizingOnScheme U
      ((ModuleDerived.pullback (hf := hφ) φ).obj ((inclusion X).obj K))

/-- `existsSurjectiveEtaleScheme K` is the existence of a surjective étale scheme chart
along which the restriction of `K` is dualizing. -/
theorem existsSurjectiveEtaleScheme_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (K : DerivedQCoh X) :
    existsSurjectiveEtaleScheme K ↔
      ∃ (U : Over S) (φ : ofOver U ⟶ X) (hφ : Etale φ) (_ : Surjective φ)
        (_ : AlgebraicGeometry.IsLocallyNoetherian U.left),
        isDualizingOnScheme U
          ((ModuleDerived.pullback (hf := hφ) φ).obj ((inclusion X).obj K)) :=
  sorry

namespace existsSurjectiveEtaleScheme

/-- A surjective étale scheme chart along which the restriction of `K` is dualizing
witnesses `existsSurjectiveEtaleScheme K`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    {K : DerivedQCoh X} {U : Over S} (φ : ofOver U ⟶ X) [Etale φ] [Surjective φ]
    [AlgebraicGeometry.IsLocallyNoetherian U.left]
    (hK : isDualizingOnScheme U
      ((ModuleDerived.pullback φ).obj ((inclusion X).obj K))) :
    existsSurjectiveEtaleScheme K :=
  sorry

/-- An object satisfying `existsSurjectiveEtaleScheme K` admits a surjective étale
scheme chart along which its restriction is dualizing. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    {K : DerivedQCoh X} (h : existsSurjectiveEtaleScheme K) :
    ∃ (U : Over S) (φ : ofOver U ⟶ X) (hφ : Etale φ) (_ : Surjective φ)
      (_ : AlgebraicGeometry.IsLocallyNoetherian U.left),
      isDualizingOnScheme U
        ((ModuleDerived.pullback (hf := hφ) φ).obj ((inclusion X).obj K)) :=
  sorry

end existsSurjectiveEtaleScheme

end DerivedQCoh

end AlgebraicGeometry.AlgebraicSpace
