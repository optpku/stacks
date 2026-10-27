/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.FiniteTypeApproximation.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 70.23.9 (1): in Situation 70.23.1, a cartesian square of algebraic
spaces quasi-separated and of finite type over B, each equipped with a
70.23.2.1 good diagram and the corresponding Lemma 70.23.4 limit system and
descended inverse-system morphisms, is eventually stagewise commutative, and
the comparison (q_i, p_i) is a closed immersion into the stagewise fibre
product. -/
@[stacks 0CPF] #check
  (AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationLimitSystem.exists_eventually_pullback_closedImmersion :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (hc : IsLimit c)
      [∀ j : I, IsNoetherian (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
      {i₀ : I}
      {X1sys X2sys X3sys X4sys : Over (OrderDual.toDual i₀) ⥤ AlgebraicSpace S}
      (x1Cone : Cone X1sys) (x2Cone : Cone X2sys)
      (x3Cone : Cone X3sys) (x4Cone : Cone X4sys)
      (x1ToS : x1Cone.pt ⟶ c.pt) (x2ToS : x2Cone.pt ⟶ c.pt)
      (x3ToS : x3Cone.pt ⟶ c.pt) (x4ToS : x4Cone.pt ⟶ c.pt)
      [QuasiSeparated x1ToS] [FiniteType x1ToS]
      [QuasiSeparated x2ToS] [FiniteType x2ToS]
      [QuasiSeparated x3ToS] [FiniteType x3ToS]
      [QuasiSeparated x4ToS] [FiniteType x4ToS]
      (X1approx : FiniteTypeApproximationLimitSystem D c i₀ X1sys x1Cone x1ToS)
      (X2approx : FiniteTypeApproximationLimitSystem D c i₀ X2sys x2Cone x2ToS)
      (X3approx : FiniteTypeApproximationLimitSystem D c i₀ X3sys x3Cone x3ToS)
      (X4approx : FiniteTypeApproximationLimitSystem D c i₀ X4sys x4Cone x4ToS)
      (φp : InverseSystemMorphismOverBase D i₀ X1sys X3sys X1approx.toBase X3approx.toBase)
      (φq : InverseSystemMorphismOverBase D i₀ X1sys X2sys X1approx.toBase X2approx.toBase)
      (φa : InverseSystemMorphismOverBase D i₀ X3sys X4sys X3approx.toBase X4approx.toBase)
      (φb : InverseSystemMorphismOverBase D i₀ X2sys X4sys X2approx.toBase X4approx.toBase)
      (p : x1Cone.pt ⟶ x3Cone.pt) (q : x1Cone.pt ⟶ x2Cone.pt)
      (a : x3Cone.pt ⟶ x4Cone.pt) (b : x2Cone.pt ⟶ x4Cone.pt)
      (hp_overS : p ≫ x3ToS = x1ToS) (hq_overS : q ≫ x2ToS = x1ToS)
      (ha_overS : a ≫ x4ToS = x3ToS) (hb_overS : b ≫ x4ToS = x2ToS)
      (hp_limit : φp.IsLimitMorphism x1Cone x3Cone p)
      (hq_limit : φq.IsLimitMorphism x1Cone x2Cone q)
      (ha_limit : φa.IsLimitMorphism x3Cone x4Cone a)
      (hb_limit : φb.IsLimitMorphism x2Cone x4Cone b)
      (hcart : IsPullback p q a b),
      ∃ (i₉ : I) (hi₀i₉ : i₀ ≤ i₉),
        AlgebraicGeometry.AlgebraicSpace.InverseSystemMorphismOverBase.PullbackClosedImmersionAt
          hi₀i₉ φp φq φa φb)

/- Lemma 70.23.9 (2): if in addition a and b are flat and of finite
presentation, then the comparison (q_i, p_i) is eventually an isomorphism. -/
@[stacks 0CPF] #check
  (AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationLimitSystem.exists_eventually_pullback_isIso :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (hc : IsLimit c)
      [∀ j : I, IsNoetherian (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
      {i₀ : I}
      {X1sys X2sys X3sys X4sys : Over (OrderDual.toDual i₀) ⥤ AlgebraicSpace S}
      (x1Cone : Cone X1sys) (x2Cone : Cone X2sys)
      (x3Cone : Cone X3sys) (x4Cone : Cone X4sys)
      (x1ToS : x1Cone.pt ⟶ c.pt) (x2ToS : x2Cone.pt ⟶ c.pt)
      (x3ToS : x3Cone.pt ⟶ c.pt) (x4ToS : x4Cone.pt ⟶ c.pt)
      [QuasiSeparated x1ToS] [FiniteType x1ToS]
      [QuasiSeparated x2ToS] [FiniteType x2ToS]
      [QuasiSeparated x3ToS] [FiniteType x3ToS]
      [QuasiSeparated x4ToS] [FiniteType x4ToS]
      (X1approx : FiniteTypeApproximationLimitSystem D c i₀ X1sys x1Cone x1ToS)
      (X2approx : FiniteTypeApproximationLimitSystem D c i₀ X2sys x2Cone x2ToS)
      (X3approx : FiniteTypeApproximationLimitSystem D c i₀ X3sys x3Cone x3ToS)
      (X4approx : FiniteTypeApproximationLimitSystem D c i₀ X4sys x4Cone x4ToS)
      (φp : InverseSystemMorphismOverBase D i₀ X1sys X3sys X1approx.toBase X3approx.toBase)
      (φq : InverseSystemMorphismOverBase D i₀ X1sys X2sys X1approx.toBase X2approx.toBase)
      (φa : InverseSystemMorphismOverBase D i₀ X3sys X4sys X3approx.toBase X4approx.toBase)
      (φb : InverseSystemMorphismOverBase D i₀ X2sys X4sys X2approx.toBase X4approx.toBase)
      (p : x1Cone.pt ⟶ x3Cone.pt) (q : x1Cone.pt ⟶ x2Cone.pt)
      (a : x3Cone.pt ⟶ x4Cone.pt) (b : x2Cone.pt ⟶ x4Cone.pt)
      (hp_overS : p ≫ x3ToS = x1ToS) (hq_overS : q ≫ x2ToS = x1ToS)
      (ha_overS : a ≫ x4ToS = x3ToS) (hb_overS : b ≫ x4ToS = x2ToS)
      (hp_limit : φp.IsLimitMorphism x1Cone x3Cone p)
      (hq_limit : φq.IsLimitMorphism x1Cone x2Cone q)
      (ha_limit : φa.IsLimitMorphism x3Cone x4Cone a)
      (hb_limit : φb.IsLimitMorphism x2Cone x4Cone b)
      (hcart : IsPullback p q a b)
      [Flat a] [FinitePresentation a] [Flat b] [FinitePresentation b],
      ∃ (i₁₀ : I) (hi₀i₁₀ : i₀ ≤ i₁₀)
        (hcomm : ∀ (i : I) (hi₁₀i : i₁₀ ≤ i),
          φp.hom.app (tailObject i (le_trans hi₀i₁₀ hi₁₀i)) ≫
            φa.hom.app (tailObject i (le_trans hi₀i₁₀ hi₁₀i)) =
          φq.hom.app (tailObject i (le_trans hi₀i₁₀ hi₁₀i)) ≫
            φb.hom.app (tailObject i (le_trans hi₀i₁₀ hi₁₀i))),
        ∀ (i : I) (hi₁₀i : i₁₀ ≤ i),
          IsIso (InverseSystemMorphismOverBase.pullbackComparison φp φq φa φb
            (tailObject i (le_trans hi₀i₁₀ hi₁₀i)) (hcomm i hi₁₀i)))
