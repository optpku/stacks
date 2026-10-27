/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Map.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Map.OnTarget

/-!
# Closed-immersion criteria for relative projective-spectrum maps of algebraic spaces

This file gives the full-domain, closed-immersion, and twist-epimorphism
consequences of eventual degreewise epimorphy for an étale-compatible relative
projective-spectrum map of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProjMap

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {𝒜 ℬ : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
variable [𝒜.IsQuasicoherent] [ℬ.IsQuasicoherent]
variable [𝒜.IsCommutative] [ℬ.IsCommutative]
variable {degA : DegreePieces 𝒜} {degB : DegreePieces ℬ}

/-- Eventual epimorphy of the nonnegative graded pieces makes the natural-domain
inclusion of an étale-compatible relative projective-spectrum map invertible. -/
theorem domain_isIso_of_eventually_surjective
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
    (hφsurj : ∃ N : ℕ, ∀ d ≥ N, Epi (φ.hom (Int.ofNat d))) :
    IsIso r.domain.ι :=
  sorry

/-- Eventual epimorphy of the nonnegative graded pieces makes the full-source
morphism of an étale-compatible relative projective-spectrum map a closed
immersion. -/
theorem mapOfFullDomain_isClosedImmersion_of_eventually_surjective
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
    (hφsurj : ∃ N : ℕ, ∀ d ≥ N, Epi (φ.hom (Int.ofNat d))) :
    let hFull :=
      domain_isIso_of_eventually_surjective FA hFA FB hFB φ r hcompat hφsurj
    AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion (mapOfFullDomain r hFull) :=
  sorry

/-- Eventual epimorphy of the nonnegative graded pieces makes every full-source
integral-twist comparison of an étale-compatible relative projective-spectrum map
an epimorphism. -/
theorem thetaOfFullDomain_epi_of_eventually_surjective
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
    (n : ℤ) :
    let hFull :=
      domain_isIso_of_eventually_surjective FA hFA FB hFB φ r hcompat hφsurj
    Epi (thetaOfFullDomain r hFull n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProjMap
