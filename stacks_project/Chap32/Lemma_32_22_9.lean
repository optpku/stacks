/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

/- Lemma 32.22.9 (1): a cartesian square on the limits of four finite-type approximation
systems is eventually represented by a commuting square whose canonical comparison to the
stagewise pullback is a closed immersion. -/
@[stacks 0CNW] #check
  (AlgebraicGeometry.FinitePresentationApproximationLimitSystem.exists_eventually_isClosedImmersion_pullbackComparison :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ j : I, IsNoetherian (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
      {i₀ : I}
      {X1sys X2sys X3sys X4sys : TailIndexCategory i₀ ⥤ Scheme.{u}}
      (x1Cone : Cone X1sys) (x2Cone : Cone X2sys)
      (x3Cone : Cone X3sys) (x4Cone : Cone X4sys)
      (x1ToBase : X1sys ⟶ tailBaseDiagram D i₀)
      (x2ToBase : X2sys ⟶ tailBaseDiagram D i₀)
      (x3ToBase : X3sys ⟶ tailBaseDiagram D i₀)
      (x4ToBase : X4sys ⟶ tailBaseDiagram D i₀)
      (x1ToS : x1Cone.pt ⟶ c.pt) (x2ToS : x2Cone.pt ⟶ c.pt)
      (x3ToS : x3Cone.pt ⟶ c.pt) (x4ToS : x4Cone.pt ⟶ c.pt)
      (x1Cone_toBase : ∀ j : TailIndexCategory i₀,
        x1Cone.π.app j ≫ x1ToBase.app j = x1ToS ≫ c.π.app j.left)
      (x2Cone_toBase : ∀ j : TailIndexCategory i₀,
        x2Cone.π.app j ≫ x2ToBase.app j = x2ToS ≫ c.π.app j.left)
      (x3Cone_toBase : ∀ j : TailIndexCategory i₀,
        x3Cone.π.app j ≫ x3ToBase.app j = x3ToS ≫ c.π.app j.left)
      (x4Cone_toBase : ∀ j : TailIndexCategory i₀,
        x4Cone.π.app j ≫ x4ToBase.app j = x4ToS ≫ c.π.app j.left)
      [QuasiSeparated x1ToS] [QuasiCompact x1ToS] [LocallyOfFiniteType x1ToS]
      [QuasiSeparated x2ToS] [QuasiCompact x2ToS] [LocallyOfFiniteType x2ToS]
      [QuasiSeparated x3ToS] [QuasiCompact x3ToS] [LocallyOfFiniteType x3ToS]
      [QuasiSeparated x4ToS] [QuasiCompact x4ToS] [LocallyOfFiniteType x4ToS]
      (X1approx : FinitePresentationApproximationLimitSystem D c i₀ X1sys x1Cone x1ToS)
      (X2approx : FinitePresentationApproximationLimitSystem D c i₀ X2sys x2Cone x2ToS)
      (X3approx : FinitePresentationApproximationLimitSystem D c i₀ X3sys x3Cone x3ToS)
      (X4approx : FinitePresentationApproximationLimitSystem D c i₀ X4sys x4Cone x4ToS)
      (p : x1Cone.pt ⟶ x3Cone.pt) (q : x1Cone.pt ⟶ x2Cone.pt)
      (a : x3Cone.pt ⟶ x4Cone.pt) (b : x2Cone.pt ⟶ x4Cone.pt)
      (hp_overS : p ≫ x3ToS = x1ToS) (hq_overS : q ≫ x2ToS = x1ToS)
      (ha_overS : a ≫ x4ToS = x3ToS) (hb_overS : b ≫ x4ToS = x2ToS)
      (hcart : IsPullback q p b a)
      (φp : InverseSystemMorphismOverBase D i₀ X1sys X3sys x1ToBase x3ToBase)
      (φq : InverseSystemMorphismOverBase D i₀ X1sys X2sys x1ToBase x2ToBase)
      (φa : InverseSystemMorphismOverBase D i₀ X3sys X4sys x3ToBase x4ToBase)
      (φb : InverseSystemMorphismOverBase D i₀ X2sys X4sys x2ToBase x4ToBase)
      (hφp : φp.IsLimitMorphism x1Cone x3Cone p)
      (hφq : φq.IsLimitMorphism x1Cone x2Cone q)
      (hφa : φa.IsLimitMorphism x3Cone x4Cone a)
      (hφb : φb.IsLimitMorphism x2Cone x4Cone b),
      ∃ (i₉ : I) (hi₀i₉ : i₀ ≤ i₉), ∀ ⦃i : I⦄ (hi₉i : i₉ ≤ i),
        ∃ hcomm :
          φq.hom.app (tailObject i (le_trans hi₀i₉ hi₉i)) ≫
              φb.hom.app (tailObject i (le_trans hi₀i₉ hi₉i)) =
            φp.hom.app (tailObject i (le_trans hi₀i₉ hi₉i)) ≫
              φa.hom.app (tailObject i (le_trans hi₀i₉ hi₉i)),
          IsClosedImmersion
            (pullback.lift
              (φq.hom.app (tailObject i (le_trans hi₀i₉ hi₉i)))
              (φp.hom.app (tailObject i (le_trans hi₀i₉ hi₉i))) hcomm))

/- Lemma 32.22.9 (2): if the two morphisms to the common target are flat and of finite
presentation, then beyond any prescribed stage the canonical comparison to the stagewise
pullback is eventually an isomorphism. -/
@[stacks 0CNW] #check
  (AlgebraicGeometry.FinitePresentationApproximationLimitSystem.exists_eventually_isIso_pullbackComparison_of_flat :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ j : I, IsNoetherian (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
      {i₀ : I}
      {X1sys X2sys X3sys X4sys : TailIndexCategory i₀ ⥤ Scheme.{u}}
      (x1Cone : Cone X1sys) (x2Cone : Cone X2sys)
      (x3Cone : Cone X3sys) (x4Cone : Cone X4sys)
      (x1ToBase : X1sys ⟶ tailBaseDiagram D i₀)
      (x2ToBase : X2sys ⟶ tailBaseDiagram D i₀)
      (x3ToBase : X3sys ⟶ tailBaseDiagram D i₀)
      (x4ToBase : X4sys ⟶ tailBaseDiagram D i₀)
      (x1ToS : x1Cone.pt ⟶ c.pt) (x2ToS : x2Cone.pt ⟶ c.pt)
      (x3ToS : x3Cone.pt ⟶ c.pt) (x4ToS : x4Cone.pt ⟶ c.pt)
      (x1Cone_toBase : ∀ j : TailIndexCategory i₀,
        x1Cone.π.app j ≫ x1ToBase.app j = x1ToS ≫ c.π.app j.left)
      (x2Cone_toBase : ∀ j : TailIndexCategory i₀,
        x2Cone.π.app j ≫ x2ToBase.app j = x2ToS ≫ c.π.app j.left)
      (x3Cone_toBase : ∀ j : TailIndexCategory i₀,
        x3Cone.π.app j ≫ x3ToBase.app j = x3ToS ≫ c.π.app j.left)
      (x4Cone_toBase : ∀ j : TailIndexCategory i₀,
        x4Cone.π.app j ≫ x4ToBase.app j = x4ToS ≫ c.π.app j.left)
      [QuasiSeparated x1ToS] [QuasiCompact x1ToS] [LocallyOfFiniteType x1ToS]
      [QuasiSeparated x2ToS] [QuasiCompact x2ToS] [LocallyOfFiniteType x2ToS]
      [QuasiSeparated x3ToS] [QuasiCompact x3ToS] [LocallyOfFiniteType x3ToS]
      [QuasiSeparated x4ToS] [QuasiCompact x4ToS] [LocallyOfFiniteType x4ToS]
      (X1approx : FinitePresentationApproximationLimitSystem D c i₀ X1sys x1Cone x1ToS)
      (X2approx : FinitePresentationApproximationLimitSystem D c i₀ X2sys x2Cone x2ToS)
      (X3approx : FinitePresentationApproximationLimitSystem D c i₀ X3sys x3Cone x3ToS)
      (X4approx : FinitePresentationApproximationLimitSystem D c i₀ X4sys x4Cone x4ToS)
      (p : x1Cone.pt ⟶ x3Cone.pt) (q : x1Cone.pt ⟶ x2Cone.pt)
      (a : x3Cone.pt ⟶ x4Cone.pt) (b : x2Cone.pt ⟶ x4Cone.pt)
      (hp_overS : p ≫ x3ToS = x1ToS) (hq_overS : q ≫ x2ToS = x1ToS)
      (ha_overS : a ≫ x4ToS = x3ToS) (hb_overS : b ≫ x4ToS = x2ToS)
      (hcart : IsPullback q p b a) (ha_flat : Flat a)
      (ha_fp : Scheme.Hom.FinitePresentation a) (hb_flat : Flat b)
      (hb_fp : Scheme.Hom.FinitePresentation b)
      (φp : InverseSystemMorphismOverBase D i₀ X1sys X3sys x1ToBase x3ToBase)
      (φq : InverseSystemMorphismOverBase D i₀ X1sys X2sys x1ToBase x2ToBase)
      (φa : InverseSystemMorphismOverBase D i₀ X3sys X4sys x3ToBase x4ToBase)
      (φb : InverseSystemMorphismOverBase D i₀ X2sys X4sys x2ToBase x4ToBase)
      (hφp : φp.IsLimitMorphism x1Cone x3Cone p)
      (hφq : φq.IsLimitMorphism x1Cone x2Cone q)
      (hφa : φa.IsLimitMorphism x3Cone x4Cone a)
      (hφb : φb.IsLimitMorphism x2Cone x4Cone b)
      (i₉ : I) (hi₀i₉ : i₀ ≤ i₉),
      ∃ (i₁₀ : I) (hi₉i₁₀ : i₉ ≤ i₁₀), ∀ ⦃i : I⦄ (hi₁₀i : i₁₀ ≤ i),
        ∃ hcomm :
          φq.hom.app (tailObject i (le_trans hi₀i₉ (le_trans hi₉i₁₀ hi₁₀i))) ≫
              φb.hom.app (tailObject i (le_trans hi₀i₉ (le_trans hi₉i₁₀ hi₁₀i))) =
            φp.hom.app (tailObject i (le_trans hi₀i₉ (le_trans hi₉i₁₀ hi₁₀i))) ≫
              φa.hom.app (tailObject i (le_trans hi₀i₉ (le_trans hi₉i₁₀ hi₁₀i))),
          IsIso
            (pullback.lift
              (φq.hom.app (tailObject i (le_trans hi₀i₉ (le_trans hi₉i₁₀ hi₁₀i))))
              (φp.hom.app (tailObject i (le_trans hi₀i₉ (le_trans hi₉i₁₀ hi₁₀i)))) hcomm))
