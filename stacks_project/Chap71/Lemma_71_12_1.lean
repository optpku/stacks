/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Map.Etale

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open AlgebraicGeometry.AlgebraicSpace.RelativeProjMap
open CategoryTheory SheafOfModules.RingedSite

universe u

/- Lemma 71.12.1: A map of quasi-coherent graded algebras on an algebraic space
induces an open domain in the target relative Proj, a morphism to the source
relative Proj over the base, and an integral graded Serre-twist algebra map.
The triple agrees with the scheme construction after every étale scheme base
change and is characterized up to the unique compatible domain isomorphism. -/
@[stacks 085F] #check (AlgebraicGeometry.AlgebraicSpace.RelativeProjMap.exists_of_etale :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 ℬ : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    [𝒜.IsQuasicoherent] [ℬ.IsQuasicoherent]
    [𝒜.IsCommutative] [ℬ.IsCommutative]
    {degA : DegreePieces 𝒜} {degB : DegreePieces ℬ}
    (FA : ProjFunctor X 𝒜) (hFA : FA.IsAssociatedToQuadruples degA)
    (FB : ProjFunctor X ℬ) (hFB : FB.IsAssociatedToQuadruples degB)
    (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ),
    ∃ r : RelativeProjMap (toAlgebraicSpace_hom FA hFA) (toAlgebraicSpace_hom FB hFB)
        𝒜 ℬ (CanonicalTwists.family FA hFA).obj (CanonicalTwists.family FB hFB).obj φ,
      (∀ (W : Over S) (g : ofOver W ⟶ X) [Etale g]
        [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
        [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)],
        Nonempty (EtaleChartCompatibility hFA hFB r g)) ∧
      IsGradedAlgebraMap r ∧
      ∀ r', (∀ (W : Over S) (g : ofOver W ⟶ X) [Etale g]
        [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
        [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)],
        Nonempty (EtaleChartCompatibility hFA hFB r' g)) → Equivalent r' r)
