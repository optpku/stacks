/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Map.ClosedImmersion

/-!
# Lemma 71.12.3

With the Lemma 71.12.1 setup, if 𝒜_d ⟶ ℬ_d is surjective for d ≫ 0, then
U(ψ) = Q, r_ψ : Q ⟶ P is a closed immersion, and each
θ : r_ψ^* 𝒪_P(n) ⟶ 𝒪_Q(n) is surjective, but not an isomorphism in general
even if 𝒜 ⟶ ℬ is surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open AlgebraicGeometry.AlgebraicSpace.RelativeProjMap
open SheafOfModules.RingedSite

universe u

/- Lemma 71.12.3 (1)
With hypotheses and notation as in Lemma 71.12.1, if 𝒜_d ⟶ ℬ_d is an
epimorphism for d ≫ 0, then U(ψ) = Q.
-/
@[stacks 085H] #check (AlgebraicGeometry.AlgebraicSpace.RelativeProjMap.domain_isIso_of_eventually_surjective :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 ℬ : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    [𝒜.IsQuasicoherent] [ℬ.IsQuasicoherent]
    [𝒜.IsCommutative] [ℬ.IsCommutative]
    {degA : DegreePieces 𝒜} {degB : DegreePieces ℬ}
    (FA : ProjFunctor X 𝒜) (hFA : FA.IsAssociatedToQuadruples degA)
    (FB : ProjFunctor X ℬ) (hFB : FB.IsAssociatedToQuadruples degB)
    (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    (r : RelativeProjMap (toAlgebraicSpace_hom FA hFA) (toAlgebraicSpace_hom FB hFB)
      𝒜 ℬ (CanonicalTwists.family FA hFA).obj (CanonicalTwists.family FB hFB).obj φ)
    (hcompat :
      ∀ (W : Over S) (g : ofOver W ⟶ X) [Etale g]
        [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
        [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)],
        Nonempty (EtaleChartCompatibility hFA hFB r g))
    (hφsurj : ∃ N : ℕ, ∀ d ≥ N, Epi (φ.hom (Int.ofNat d))),
    IsIso r.domain.ι)

/- Lemma 71.12.3 (2)
The induced morphism r_ψ : Q ⟶ P is a closed immersion.
-/
@[stacks 085H] #check (AlgebraicGeometry.AlgebraicSpace.RelativeProjMap.mapOfFullDomain_isClosedImmersion_of_eventually_surjective :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 ℬ : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    [𝒜.IsQuasicoherent] [ℬ.IsQuasicoherent]
    [𝒜.IsCommutative] [ℬ.IsCommutative]
    {degA : DegreePieces 𝒜} {degB : DegreePieces ℬ}
    (FA : ProjFunctor X 𝒜) (hFA : FA.IsAssociatedToQuadruples degA)
    (FB : ProjFunctor X ℬ) (hFB : FB.IsAssociatedToQuadruples degB)
    (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    (r : RelativeProjMap (toAlgebraicSpace_hom FA hFA) (toAlgebraicSpace_hom FB hFB)
      𝒜 ℬ (CanonicalTwists.family FA hFA).obj (CanonicalTwists.family FB hFB).obj φ)
    (hcompat :
      ∀ (W : Over S) (g : ofOver W ⟶ X) [Etale g]
        [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
        [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)],
        Nonempty (EtaleChartCompatibility hFA hFB r g))
    (hφsurj : ∃ N : ℕ, ∀ d ≥ N, Epi (φ.hom (Int.ofNat d))),
    let hFull :=
      domain_isIso_of_eventually_surjective FA hFA FB hFB φ r hcompat hφsurj
    AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion (mapOfFullDomain r hFull))

/- Lemma 71.12.3 (3)
The maps θ : r_ψ^* 𝒪_P(n) ⟶ 𝒪_Q(n) are surjective, but not isomorphisms in
general (even if 𝒜 ⟶ ℬ is surjective).
-/
@[stacks 085H] #check (AlgebraicGeometry.AlgebraicSpace.RelativeProjMap.thetaOfFullDomain_epi_of_eventually_surjective :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 ℬ : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    [𝒜.IsQuasicoherent] [ℬ.IsQuasicoherent]
    [𝒜.IsCommutative] [ℬ.IsCommutative]
    {degA : DegreePieces 𝒜} {degB : DegreePieces ℬ}
    (FA : ProjFunctor X 𝒜) (hFA : FA.IsAssociatedToQuadruples degA)
    (FB : ProjFunctor X ℬ) (hFB : FB.IsAssociatedToQuadruples degB)
    (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    (r : RelativeProjMap (toAlgebraicSpace_hom FA hFA) (toAlgebraicSpace_hom FB hFB)
      𝒜 ℬ (CanonicalTwists.family FA hFA).obj (CanonicalTwists.family FB hFB).obj φ)
    (hcompat :
      ∀ (W : Over S) (g : ofOver W ⟶ X) [Etale g]
        [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
        [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)],
        Nonempty (EtaleChartCompatibility hFA hFB r g))
    (hφsurj : ∃ N : ℕ, ∀ d ≥ N, Epi (φ.hom (Int.ofNat d)))
    (n : ℤ),
    let hFull :=
      domain_isIso_of_eventually_surjective FA hFA FB hFB φ r hcompat hφsurj
    Epi (thetaOfFullDomain r hFull n))
