/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Lemma_71_12_1_Compatibility
public import stacks_project.Chap71.Lemma_71_12_3_OnTarget

/-!
# Isomorphism criteria for relative projective-spectrum maps of algebraic spaces

This file gives the full-domain and isomorphism consequences of eventual degreewise
isomorphy for an étale-compatible relative projective-spectrum map.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
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

/-- Eventual isomorphy of the nonnegative graded pieces makes the natural domain of an
étale-compatible relative projective-spectrum map equal to the identity open on the
source. -/
theorem domain_eq_id_of_eventually_isIso
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
    (hφIso : ∃ N : ℕ, ∀ d ≥ N, IsIso (φ.hom (Int.ofNat d))) :
    r.domain = OpenSubspace.id (toAlgebraicSpace FB hFB) :=
  sorry

/-- Eventual isomorphy of the nonnegative graded pieces makes the full-source morphism of
an étale-compatible relative projective-spectrum map an isomorphism. -/
theorem mapOnTarget_isIso_of_eventually_isIso
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
    (hφIso : ∃ N : ℕ, ∀ d ≥ N, IsIso (φ.hom (Int.ofNat d))) :
    let hId := domain_eq_id_of_eventually_isIso r hcompat hφIso
    IsIso (mapOnTarget r hId) :=
  sorry

/-- Eventual isomorphy of the nonnegative graded pieces makes every full-source
integral-twist comparison of an étale-compatible relative projective-spectrum map an
isomorphism. -/
theorem thetaOnTarget_isIso_of_eventually_isIso
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
    (n : ℤ) :
    let hId := domain_eq_id_of_eventually_isIso r hcompat hφIso
    let hι := domainTopInclusion_comp_ι r hId
    IsIso (thetaOnTarget r hId hι n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProjMap
