/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Crystalline.Functoriality

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Crystalline

universe u

variable {p : ℕ} [Fact (Nat.Prime p)] (B B' : Base.{u} p)
variable (f : B.source ⟶ B'.source)
variable (g : DividedPowerSchemeHom B.ideal B'.ideal B.toSpec B'.toSpec)
variable (h_comm : f ≫ B'.sourceToClosed = B.sourceToClosed ≫ g.zeroFiberMap)
variable (h_dividedPowers_compatible :
  ∀ (V : B'.scheme.affineOpens) (W : B.scheme.affineOpens)
    (hVW : W.1 ≤ g.base ⁻¹ᵁ V.1),
    (B'.dividedPowers V).IsDPMorphism (B.dividedPowers W) (g.base.appLE V W hVW).hom)

/- Remark 60.8.5 (Functoriality)
A divided-power base morphism and a commuting source square induce the geometric
morphism from the crystalline topos of the source to that of the target. -/
@[stacks 07IC] #check (AlgebraicGeometry.Scheme.Crystalline.functorialToposHom
    B B' f g h_comm h_dividedPowers_compatible :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u + 1}
      (crystallineZariskiTopology B'.scheme B'.ideal B'.dividedPowers B'.compatible B'.source B'.sourceToClosed)
      (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible B.source B.sourceToClosed))

#check (AlgebraicGeometry.crystallineFunctor_isContinuous
    B.ideal B'.ideal B.dividedPowers B'.dividedPowers B.compatible B'.compatible
    B.toSpec B'.toSpec B.sourceToClosed B'.sourceToClosed f g h_comm
    h_dividedPowers_compatible B.prime_nilpotent B'.prime_nilpotent :
    (CrystallineFunctor.of f g h_comm B.prime_nilpotent B'.prime_nilpotent
      h_dividedPowers_compatible).toRelativeFunctor.IsContinuous
      (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible B.source B.sourceToClosed)
      (crystallineZariskiTopology B'.scheme B'.ideal B'.dividedPowers B'.compatible B'.source B'.sourceToClosed))

#check (AlgebraicGeometry.crystallineFunctor_isCocontinuous
    B.ideal B'.ideal B.dividedPowers B'.dividedPowers B.compatible B'.compatible
    B.toSpec B'.toSpec B.sourceToClosed B'.sourceToClosed f g h_comm
    h_dividedPowers_compatible B.prime_nilpotent B'.prime_nilpotent :
    (CrystallineFunctor.of f g h_comm B.prime_nilpotent B'.prime_nilpotent
      h_dividedPowers_compatible).toRelativeFunctor.IsCocontinuous
      (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible B.source B.sourceToClosed)
      (crystallineZariskiTopology B'.scheme B'.ideal B'.dividedPowers B'.compatible B'.source B'.sourceToClosed))
