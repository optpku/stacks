/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Crystalline.Zariski
public import ReasLib.AlgebraicGeometry.Crystalline.Limits

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Crystalline

universe u v w

/- Remark 60.8.6 (Comparison with Zariski site): the source-forgetting functor
induces a morphism from the big crystalline topos to the big Zariski topos. -/
@[stacks 07ID] #check (AlgebraicGeometry.Scheme.Crystalline.Base.zariskiToposMorphism :
    ∀ {p : ℕ} [Fact p.Prime] (B : AlgebraicGeometry.Scheme.Crystalline.Base.{u} p),
      MorphismOfTopoiIn.{_, _, _, _, u + 1} B.source.bigZariskiTopology
        (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible
          B.source B.sourceToClosed))

variable {p : ℕ} [Fact p.Prime] (B : AlgebraicGeometry.Scheme.Crystalline.Base.{u} p)

/- Cocontinuity uses the quasi-coherent ideal of the prime-local crystalline base. -/
#check (AlgebraicGeometry.Scheme.Crystalline.crystallineForgetful_isCocontinuous
    B.scheme B.ideal (h_quasiCoherent := B.quasiCoherent)
    B.dividedPowers B.compatible B.toSpec B.source B.sourceToClosed B.prime_nilpotent :
      (crystallineForgetful B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
        B.source B.sourceToClosed B.prime_nilpotent).IsCocontinuous
        (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible
          B.source B.sourceToClosed) B.source.bigZariskiTopology)

/- Preservation of all existing limits includes products and fibred products. -/
#check (AlgebraicGeometry.Scheme.Crystalline.Base.forgetful_preservesLimits :
    ∀ {p : ℕ} [Fact p.Prime] (B : AlgebraicGeometry.Scheme.Crystalline.Base.{u} p),
      PreservesLimitsOfSize.{v, w}
        (crystallineForgetful B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
          B.source B.sourceToClosed B.prime_nilpotent))

