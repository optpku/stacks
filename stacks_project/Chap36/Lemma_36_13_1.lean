/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback.EssentiallySurjective

@[expose] public section

open CategoryTheory

universe u

/- Lemma 36.13.1 (1): restriction from `D_QCoh(𝒪_X)` to `D_QCoh(𝒪_U)` along a
quasi-compact open immersion `j : U ⟶ X` is essentially surjective. -/
@[stacks 08ED] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.OpenImmersion.pullbackEssSurj :
    ∀ {X U : AlgebraicGeometry.Scheme.{u}} (j : U ⟶ X)
      [AlgebraicGeometry.IsOpenImmersion j] [AlgebraicGeometry.QuasiCompact j],
      (AlgebraicGeometry.Scheme.DerivedQCoh.OpenImmersion.pullback j).EssSurj)

/- Lemma 36.13.1 (2): restriction from `D⁺_QCoh(𝒪_X)` to `D⁺_QCoh(𝒪_U)` along a
quasi-compact open immersion `j : U ⟶ X` is essentially surjective. -/
@[stacks 08ED] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.OpenImmersion.pullbackPlusEssSurj :
    ∀ {X U : AlgebraicGeometry.Scheme.{u}} (j : U ⟶ X)
      [AlgebraicGeometry.IsOpenImmersion j] [AlgebraicGeometry.QuasiCompact j],
      (AlgebraicGeometry.Scheme.DerivedQCoh.OpenImmersion.pullbackPlus j).EssSurj)

/- Lemma 36.13.1 (3): if `X` is quasi-compact, restriction from `D⁻_QCoh(𝒪_X)` to
`D⁻_QCoh(𝒪_U)` along a quasi-compact open immersion `j : U ⟶ X` is essentially
surjective. -/
@[stacks 08ED] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.OpenImmersion.pullbackMinusEssSurj :
    ∀ {X U : AlgebraicGeometry.Scheme.{u}} (j : U ⟶ X)
      [AlgebraicGeometry.IsOpenImmersion j] [AlgebraicGeometry.QuasiCompact j]
      [CompactSpace X],
      (AlgebraicGeometry.Scheme.DerivedQCoh.OpenImmersion.pullbackMinus j).EssSurj)

/- Lemma 36.13.1 (4): if `X` is quasi-compact, restriction from `Dᵇ_QCoh(𝒪_X)` to
`Dᵇ_QCoh(𝒪_U)` along a quasi-compact open immersion `j : U ⟶ X` is essentially
surjective. -/
@[stacks 08ED] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.OpenImmersion.pullbackBoundedEssSurj :
    ∀ {X U : AlgebraicGeometry.Scheme.{u}} (j : U ⟶ X)
      [AlgebraicGeometry.IsOpenImmersion j] [AlgebraicGeometry.QuasiCompact j]
      [CompactSpace X],
      (AlgebraicGeometry.Scheme.DerivedQCoh.OpenImmersion.pullbackBounded j).EssSurj)
