/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Map.DegreeOneGenerated

/-!
# Lemma 71.12.5

Eventual surjectivity of a map of quasi-coherent graded `𝒪_X`-algebras together with
degree-one generation of the source makes the induced relative projective-spectrum map
a closed immersion from the full source, with isomorphic twist comparisons.

Invertibility of the canonical open inclusion expresses the full-domain assertion
independently of the chosen presentation of the open subspace. The first two
conclusions already follow from eventual surjectivity alone.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open AlgebraicGeometry.AlgebraicSpace.RelativeProjMap
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProjMap

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {𝒜 ℬ : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
variable [𝒜.IsQuasicoherent] [ℬ.IsQuasicoherent]
variable [𝒜.IsCommutative] [ℬ.IsCommutative]
variable {degA : DegreePieces 𝒜} {degB : DegreePieces ℬ}

/- Lemma 71.12.5 (1)
The natural domain is the full source: its canonical open inclusion is invertible.
-/
@[stacks 085J] #check
  (AlgebraicGeometry.AlgebraicSpace.RelativeProjMap.domain_isIso_of_eventually_surjective :
    ∀ (FA : ProjFunctor X 𝒜) (hFA : FA.IsAssociatedToQuadruples degA)
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

/- Lemma 71.12.5 (2)
The canonical full-source morphism is a closed immersion.
-/
@[stacks 085J] #check
  (AlgebraicGeometry.AlgebraicSpace.RelativeProjMap.mapOfFullDomain_isClosedImmersion_of_eventually_surjective :
    ∀ (FA : ProjFunctor X 𝒜) (hFA : FA.IsAssociatedToQuadruples degA)
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

/- Lemma 71.12.5 (3)
Under degree-one generation, every integral-twist comparison on the full source
is an isomorphism.
-/
@[stacks 085J] #check
  (AlgebraicGeometry.AlgebraicSpace.RelativeProjMap.thetaOfFullDomain_isIso_of_degreeOneGenerated :
    ∀ (FA : ProjFunctor X 𝒜) (hFA : FA.IsAssociatedToQuadruples degA)
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
    (hgenerated : GeneratedByDegreeOne 𝒜) (n : ℤ),
    let hFull :=
      domain_isIso_of_eventually_surjective FA hFA FB hFB φ r hcompat hφsurj
    IsIso (thetaOfFullDomain r hFull n))

end AlgebraicGeometry.AlgebraicSpace.RelativeProjMap
