/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Topos
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline

universe u

variable {p : ℕ} [Fact p.Prime]
variable (B : AlgebraicGeometry.Scheme.Crystalline.Base.{u} p)

/- Lemma 60.9.2 (1): the inclusion of the small crystalline site into the big crystalline site. -/
@[stacks 07IJ] #check (AlgebraicGeometry.Scheme.Crystalline.smallCrystallineInclusion
  B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed :
  smallCrystallineSite B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed ⥤
    RelativeCRIS B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed)

/- Lemma 60.9.2 (2): the inclusion preserves finite nonempty limits. -/
@[stacks 07IJ] #check (AlgebraicGeometry.Scheme.Crystalline.smallCrystallineInclusion_preservesFiniteNonemptyLimits
  B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed :
  PreservesFiniteNonemptyLimits
    (smallCrystallineInclusion B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed))

/- Lemma 60.9.2 (3): the inclusion is fully faithful. -/
@[stacks 07IJ] #check (AlgebraicGeometry.Scheme.Crystalline.smallCrystallineInclusion_fullyFaithful
  B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed :
  (smallCrystallineInclusion B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed).FullyFaithful)

/- Lemma 60.9.2 (4): the inclusion is continuous for the crystalline topologies. -/
@[stacks 07IJ] #check (AlgebraicGeometry.Scheme.Crystalline.smallCrystallineInclusion_isContinuous
  B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed p B.toSpec B.prime_nilpotent :
  Functor.IsContinuous (smallCrystallineInclusion B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed)
    (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible
    B.toSpec B.source B.sourceToClosed B.prime_nilpotent)
    (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed))

/- Lemma 60.9.2 (5): the inclusion is cocontinuous for the crystalline topologies. -/
@[stacks 07IJ] #check (AlgebraicGeometry.Scheme.Crystalline.smallCrystallineInclusion_isCocontinuous
  B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed p B.toSpec B.prime_nilpotent :
  Functor.IsCocontinuous (smallCrystallineInclusion B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed)
    (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible
    B.toSpec B.source B.sourceToClosed B.prime_nilpotent)
    (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed))

/- Lemma 60.9.2 (6): the inclusion induces a morphism from the small crystalline topos to the big one. -/
@[stacks 07IJ] #check (AlgebraicGeometry.Scheme.Crystalline.smallToBigCrystallineToposMorphism
  B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed p B.toSpec B.prime_nilpotent :
  MorphismOfTopoiIn.{u + 1, u + 1, u, u, u + 1}
    (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed)
    (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible
    B.toSpec B.source B.sourceToClosed B.prime_nilpotent))

/- Lemma 60.9.2 (7): the continuous sheaf adjunction induces the reverse geometric morphism. -/
@[stacks 07IJ] #check (AlgebraicGeometry.Scheme.Crystalline.bigToSmallCrystallineToposMorphism
  B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed p B.toSpec B.prime_nilpotent :
  MorphismOfTopoiIn.{u + 1, u + 1, u, u, u + 1}
    (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible
    B.toSpec B.source B.sourceToClosed B.prime_nilpotent)
    (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed))

/- Lemma 60.9.2 (8): the composite inverse image is naturally isomorphic to the identity on the small topos. -/
@[stacks 07IJ] #check (AlgebraicGeometry.Scheme.Crystalline.bigToSmallCrystallineToposMorphism_comp_smallToBigInverseImageIso
  B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed p B.toSpec B.prime_nilpotent :
  (MorphismOfTopoiIn.comp
    (bigToSmallCrystallineToposMorphism B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed p B.toSpec B.prime_nilpotent)
    (smallToBigCrystallineToposMorphism B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed p B.toSpec B.prime_nilpotent)).inverseImage ≅
    (MorphismOfTopoiIn.id (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible
    B.toSpec B.source B.sourceToClosed B.prime_nilpotent)).inverseImage)

/- Lemma 60.9.2 (9): the reverse direct image is naturally isomorphic to the inclusion-induced inverse image. -/
@[stacks 07IJ] #check (AlgebraicGeometry.Scheme.Crystalline.bigToSmallCrystallineToposMorphism_pushforwardIso
  B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed p B.toSpec B.prime_nilpotent :
  (bigToSmallCrystallineToposMorphism B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed p B.toSpec B.prime_nilpotent).pushforward ≅
    (smallToBigCrystallineToposMorphism B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed p B.toSpec B.prime_nilpotent).inverseImage)

