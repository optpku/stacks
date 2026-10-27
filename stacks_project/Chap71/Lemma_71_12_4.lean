/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Map.Isomorphism

/-!
# Lemma 71.12.4

With the hypotheses and notation of Lemma 71.12.1, if the nonnegative graded pieces of
ψ are isomorphisms in all sufficiently large degrees, then U(ψ) equals Q, the induced
map r_ψ : Q ⟶ P is an isomorphism, and each twist comparison
θ : r_ψ^* 𝒪_P(n) ⟶ 𝒪_Q(n) is an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open AlgebraicGeometry.AlgebraicSpace.RelativeProjMap
open SheafOfModules.RingedSite

universe u

/- Lemma 71.12.4 (1)
Eventual isomorphy of 𝒜_d → ℬ_d for d ≫ 0 makes the natural domain all of Q,
expressed as invertibility of the domain inclusion.
-/
@[stacks 085I] #check (AlgebraicGeometry.AlgebraicSpace.RelativeProjMap.domain_isIso_of_eventually_isIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 ℬ : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    [𝒜.IsQuasicoherent] [ℬ.IsQuasicoherent]
    [𝒜.IsCommutative] [ℬ.IsCommutative]
    {degA : DegreePieces 𝒜} {degB : DegreePieces ℬ}
    {FA : ProjFunctor X 𝒜} {hFA : FA.IsAssociatedToQuadruples degA}
    {FB : ProjFunctor X ℬ} {hFB : FB.IsAssociatedToQuadruples degB}
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    (r : RelativeProjMap (toAlgebraicSpace_hom FA hFA) (toAlgebraicSpace_hom FB hFB)
      𝒜 ℬ (CanonicalTwists.family FA hFA).obj (CanonicalTwists.family FB hFB).obj φ)
    (hcompat :
      ∀ (W : Over S) (g : ofOver W ⟶ X) [Etale g]
        [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
        [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)],
        Nonempty (EtaleChartCompatibility hFA hFB r g))
    (hφIso : ∃ N : ℕ, ∀ d ≥ N, IsIso (φ.hom (Int.ofNat d))),
    IsIso r.domain.ι)

/- Lemma 71.12.4 (2)
The full-source morphism r_ψ : Q ⟶ P is then an isomorphism.
-/
@[stacks 085I] #check (AlgebraicGeometry.AlgebraicSpace.RelativeProjMap.mapOfFullDomain_isIso_of_eventually_isIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 ℬ : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    [𝒜.IsQuasicoherent] [ℬ.IsQuasicoherent]
    [𝒜.IsCommutative] [ℬ.IsCommutative]
    {degA : DegreePieces 𝒜} {degB : DegreePieces ℬ}
    {FA : ProjFunctor X 𝒜} {hFA : FA.IsAssociatedToQuadruples degA}
    {FB : ProjFunctor X ℬ} {hFB : FB.IsAssociatedToQuadruples degB}
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    (r : RelativeProjMap (toAlgebraicSpace_hom FA hFA) (toAlgebraicSpace_hom FB hFB)
      𝒜 ℬ (CanonicalTwists.family FA hFA).obj (CanonicalTwists.family FB hFB).obj φ)
    (hcompat :
      ∀ (W : Over S) (g : ofOver W ⟶ X) [Etale g]
        [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
        [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)],
        Nonempty (EtaleChartCompatibility hFA hFB r g))
    (hφIso : ∃ N : ℕ, ∀ d ≥ N, IsIso (φ.hom (Int.ofNat d))),
    let hFull := domain_isIso_of_eventually_isIso r hcompat hφIso
    IsIso (mapOfFullDomain r hFull))

/- Lemma 71.12.4 (3)
Each full-source integral-twist comparison θ : r_ψ^* 𝒪_P(n) ⟶ 𝒪_Q(n) is an isomorphism.
-/
@[stacks 085I] #check (AlgebraicGeometry.AlgebraicSpace.RelativeProjMap.thetaOfFullDomain_isIso_of_eventually_isIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 ℬ : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    [𝒜.IsQuasicoherent] [ℬ.IsQuasicoherent]
    [𝒜.IsCommutative] [ℬ.IsCommutative]
    {degA : DegreePieces 𝒜} {degB : DegreePieces ℬ}
    {FA : ProjFunctor X 𝒜} {hFA : FA.IsAssociatedToQuadruples degA}
    {FB : ProjFunctor X ℬ} {hFB : FB.IsAssociatedToQuadruples degB}
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    (r : RelativeProjMap (toAlgebraicSpace_hom FA hFA) (toAlgebraicSpace_hom FB hFB)
      𝒜 ℬ (CanonicalTwists.family FA hFA).obj (CanonicalTwists.family FB hFB).obj φ)
    (hcompat :
      ∀ (W : Over S) (g : ofOver W ⟶ X) [Etale g]
        [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
        [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)],
        Nonempty (EtaleChartCompatibility hFA hFB r g))
    (hφIso : ∃ N : ℕ, ∀ d ≥ N, IsIso (φ.hom (Int.ofNat d)))
    (n : ℤ),
    let hFull := domain_isIso_of_eventually_isIso r hcompat hφIso
    IsIso (thetaOfFullDomain r hFull n))
