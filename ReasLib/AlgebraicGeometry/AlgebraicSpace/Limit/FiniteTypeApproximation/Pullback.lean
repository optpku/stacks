/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.FiniteTypeApproximation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fibre-product comparisons of finite-type approximation systems

A cartesian square of quasi-separated finite-type algebraic spaces over a
directed affine limit, each presented by a finite-type approximation system,
has an eventually commutative stagewise square whose comparison into the
stagewise fibre product is a closed immersion, and is eventually an
isomorphism when the remaining two morphisms are flat of finite presentation.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace InverseSystemMorphismOverBase

/-- The comparison `(q_j, p_j)` from a stage of the source system into the
stagewise fibre product of the remaining three systems. -/
def pullbackComparison
    {I : Type u} [Preorder I] {i₀ : I} {S : Scheme.{u}}
    {D : OrderDual I ⥤ AlgebraicSpace S}
    {X1sys X2sys X3sys X4sys : Over (OrderDual.toDual i₀) ⥤ AlgebraicSpace S}
    {x1ToBase : X1sys ⟶ tailBaseDiagram D i₀}
    {x2ToBase : X2sys ⟶ tailBaseDiagram D i₀}
    {x3ToBase : X3sys ⟶ tailBaseDiagram D i₀}
    {x4ToBase : X4sys ⟶ tailBaseDiagram D i₀}
    (φp : InverseSystemMorphismOverBase D i₀ X1sys X3sys x1ToBase x3ToBase)
    (φq : InverseSystemMorphismOverBase D i₀ X1sys X2sys x1ToBase x2ToBase)
    (φa : InverseSystemMorphismOverBase D i₀ X3sys X4sys x3ToBase x4ToBase)
    (φb : InverseSystemMorphismOverBase D i₀ X2sys X4sys x2ToBase x4ToBase)
    (j : Over (OrderDual.toDual i₀))
    (hcomm : φp.hom.app j ≫ φa.hom.app j = φq.hom.app j ≫ φb.hom.app j) :
    X1sys.obj j ⟶ pullback (φb.hom.app j) (φa.hom.app j) :=
  pullback.lift (φq.hom.app j) (φp.hom.app j) hcomm.symm

/-- The first projection of the stagewise fibre-product comparison is the
stage map `q_j`. -/
theorem pullbackComparison_fst
    {I : Type u} [Preorder I] {i₀ : I} {S : Scheme.{u}}
    {D : OrderDual I ⥤ AlgebraicSpace S}
    {X1sys X2sys X3sys X4sys : Over (OrderDual.toDual i₀) ⥤ AlgebraicSpace S}
    {x1ToBase : X1sys ⟶ tailBaseDiagram D i₀}
    {x2ToBase : X2sys ⟶ tailBaseDiagram D i₀}
    {x3ToBase : X3sys ⟶ tailBaseDiagram D i₀}
    {x4ToBase : X4sys ⟶ tailBaseDiagram D i₀}
    (φp : InverseSystemMorphismOverBase D i₀ X1sys X3sys x1ToBase x3ToBase)
    (φq : InverseSystemMorphismOverBase D i₀ X1sys X2sys x1ToBase x2ToBase)
    (φa : InverseSystemMorphismOverBase D i₀ X3sys X4sys x3ToBase x4ToBase)
    (φb : InverseSystemMorphismOverBase D i₀ X2sys X4sys x2ToBase x4ToBase)
    (j : Over (OrderDual.toDual i₀))
    (hcomm : φp.hom.app j ≫ φa.hom.app j = φq.hom.app j ≫ φb.hom.app j) :
    pullbackComparison φp φq φa φb j hcomm ≫ pullback.fst (φb.hom.app j) (φa.hom.app j) =
      φq.hom.app j := sorry

/-- The second projection of the stagewise fibre-product comparison is the
stage map `p_j`. -/
theorem pullbackComparison_snd
    {I : Type u} [Preorder I] {i₀ : I} {S : Scheme.{u}}
    {D : OrderDual I ⥤ AlgebraicSpace S}
    {X1sys X2sys X3sys X4sys : Over (OrderDual.toDual i₀) ⥤ AlgebraicSpace S}
    {x1ToBase : X1sys ⟶ tailBaseDiagram D i₀}
    {x2ToBase : X2sys ⟶ tailBaseDiagram D i₀}
    {x3ToBase : X3sys ⟶ tailBaseDiagram D i₀}
    {x4ToBase : X4sys ⟶ tailBaseDiagram D i₀}
    (φp : InverseSystemMorphismOverBase D i₀ X1sys X3sys x1ToBase x3ToBase)
    (φq : InverseSystemMorphismOverBase D i₀ X1sys X2sys x1ToBase x2ToBase)
    (φa : InverseSystemMorphismOverBase D i₀ X3sys X4sys x3ToBase x4ToBase)
    (φb : InverseSystemMorphismOverBase D i₀ X2sys X4sys x2ToBase x4ToBase)
    (j : Over (OrderDual.toDual i₀))
    (hcomm : φp.hom.app j ≫ φa.hom.app j = φq.hom.app j ≫ φb.hom.app j) :
    pullbackComparison φp φq φa φb j hcomm ≫ pullback.snd (φb.hom.app j) (φa.hom.app j) =
      φp.hom.app j := sorry

/-- The comparison into the chosen stagewise fibre product is an isomorphism if
and only if the stage square is cartesian. -/
theorem isIso_pullbackComparison_iff_isPullback
    {I : Type u} [Preorder I] {i₀ : I} {S : Scheme.{u}}
    {D : OrderDual I ⥤ AlgebraicSpace S}
    {X1sys X2sys X3sys X4sys : Over (OrderDual.toDual i₀) ⥤ AlgebraicSpace S}
    {x1ToBase : X1sys ⟶ tailBaseDiagram D i₀}
    {x2ToBase : X2sys ⟶ tailBaseDiagram D i₀}
    {x3ToBase : X3sys ⟶ tailBaseDiagram D i₀}
    {x4ToBase : X4sys ⟶ tailBaseDiagram D i₀}
    (φp : InverseSystemMorphismOverBase D i₀ X1sys X3sys x1ToBase x3ToBase)
    (φq : InverseSystemMorphismOverBase D i₀ X1sys X2sys x1ToBase x2ToBase)
    (φa : InverseSystemMorphismOverBase D i₀ X3sys X4sys x3ToBase x4ToBase)
    (φb : InverseSystemMorphismOverBase D i₀ X2sys X4sys x2ToBase x4ToBase)
    (j : Over (OrderDual.toDual i₀))
    (hcomm : φp.hom.app j ≫ φa.hom.app j = φq.hom.app j ≫ φb.hom.app j) :
    IsIso (pullbackComparison φp φq φa φb j hcomm) ↔
      IsPullback (φp.hom.app j) (φq.hom.app j) (φa.hom.app j) (φb.hom.app j) := sorry

/-- Eventual commutativity of a square of inverse-system morphisms, together with
the closed-immersion property of the comparison into the stagewise fibre
product. -/
structure PullbackClosedImmersionAt
    {I : Type u} [Preorder I] {i₀ i₉ : I} {S : Scheme.{u}}
    {D : OrderDual I ⥤ AlgebraicSpace S}
    {X1sys X2sys X3sys X4sys : Over (OrderDual.toDual i₀) ⥤ AlgebraicSpace S}
    {x1ToBase : X1sys ⟶ tailBaseDiagram D i₀}
    {x2ToBase : X2sys ⟶ tailBaseDiagram D i₀}
    {x3ToBase : X3sys ⟶ tailBaseDiagram D i₀}
    {x4ToBase : X4sys ⟶ tailBaseDiagram D i₀}
    (hi₀i₉ : i₀ ≤ i₉)
    (φp : InverseSystemMorphismOverBase D i₀ X1sys X3sys x1ToBase x3ToBase)
    (φq : InverseSystemMorphismOverBase D i₀ X1sys X2sys x1ToBase x2ToBase)
    (φa : InverseSystemMorphismOverBase D i₀ X3sys X4sys x3ToBase x4ToBase)
    (φb : InverseSystemMorphismOverBase D i₀ X2sys X4sys x2ToBase x4ToBase) : Prop where
  /-- The stage square commutes at and beyond the fixed stage. -/
  comm_stage : ∀ (i : I) (hi₉i : i₉ ≤ i),
    φp.hom.app (tailObject i (le_trans hi₀i₉ hi₉i)) ≫
      φa.hom.app (tailObject i (le_trans hi₀i₉ hi₉i)) =
    φq.hom.app (tailObject i (le_trans hi₀i₉ hi₉i)) ≫
      φb.hom.app (tailObject i (le_trans hi₀i₉ hi₉i))
  /-- The comparison into the stagewise fibre product is a closed immersion at
  and beyond the fixed stage. -/
  closedImmersion_stage : ∀ (i : I) (hi₉i : i₉ ≤ i),
    IsClosedImmersion
      (pullbackComparison φp φq φa φb (tailObject i (le_trans hi₀i₉ hi₉i))
        (comm_stage i hi₉i))

namespace PullbackClosedImmersionAt

/-- Assemble eventual commutativity and the closed-immersion comparison at a
fixed stage. -/
def ofConditions
    {I : Type u} [Preorder I] {i₀ i₉ : I} {S : Scheme.{u}}
    {D : OrderDual I ⥤ AlgebraicSpace S}
    {X1sys X2sys X3sys X4sys : Over (OrderDual.toDual i₀) ⥤ AlgebraicSpace S}
    {x1ToBase : X1sys ⟶ tailBaseDiagram D i₀}
    {x2ToBase : X2sys ⟶ tailBaseDiagram D i₀}
    {x3ToBase : X3sys ⟶ tailBaseDiagram D i₀}
    {x4ToBase : X4sys ⟶ tailBaseDiagram D i₀}
    (hi₀i₉ : i₀ ≤ i₉)
    (φp : InverseSystemMorphismOverBase D i₀ X1sys X3sys x1ToBase x3ToBase)
    (φq : InverseSystemMorphismOverBase D i₀ X1sys X2sys x1ToBase x2ToBase)
    (φa : InverseSystemMorphismOverBase D i₀ X3sys X4sys x3ToBase x4ToBase)
    (φb : InverseSystemMorphismOverBase D i₀ X2sys X4sys x2ToBase x4ToBase)
    (comm_stage : ∀ (i : I) (hi₉i : i₉ ≤ i),
      φp.hom.app (tailObject i (le_trans hi₀i₉ hi₉i)) ≫
        φa.hom.app (tailObject i (le_trans hi₀i₉ hi₉i)) =
      φq.hom.app (tailObject i (le_trans hi₀i₉ hi₉i)) ≫
        φb.hom.app (tailObject i (le_trans hi₀i₉ hi₉i)))
    (closedImmersion_stage : ∀ (i : I) (hi₉i : i₉ ≤ i),
      IsClosedImmersion
        (pullbackComparison φp φq φa φb (tailObject i (le_trans hi₀i₉ hi₉i))
          (comm_stage i hi₉i))) :
    PullbackClosedImmersionAt hi₀i₉ φp φq φa φb where
  comm_stage := comm_stage
  closedImmersion_stage := closedImmersion_stage

end PullbackClosedImmersionAt

/-- The fixed-stage fibre-product closed-immersion certificate is equivalent to
eventual commutativity together with the closed-immersion property of the
stagewise comparison. -/
theorem pullbackClosedImmersionAt_iff
    {I : Type u} [Preorder I] {i₀ i₉ : I} {S : Scheme.{u}}
    {D : OrderDual I ⥤ AlgebraicSpace S}
    {X1sys X2sys X3sys X4sys : Over (OrderDual.toDual i₀) ⥤ AlgebraicSpace S}
    {x1ToBase : X1sys ⟶ tailBaseDiagram D i₀}
    {x2ToBase : X2sys ⟶ tailBaseDiagram D i₀}
    {x3ToBase : X3sys ⟶ tailBaseDiagram D i₀}
    {x4ToBase : X4sys ⟶ tailBaseDiagram D i₀}
    (hi₀i₉ : i₀ ≤ i₉)
    (φp : InverseSystemMorphismOverBase D i₀ X1sys X3sys x1ToBase x3ToBase)
    (φq : InverseSystemMorphismOverBase D i₀ X1sys X2sys x1ToBase x2ToBase)
    (φa : InverseSystemMorphismOverBase D i₀ X3sys X4sys x3ToBase x4ToBase)
    (φb : InverseSystemMorphismOverBase D i₀ X2sys X4sys x2ToBase x4ToBase) :
    PullbackClosedImmersionAt hi₀i₉ φp φq φa φb ↔
      ∃ (comm_stage : ∀ (i : I) (hi₉i : i₉ ≤ i),
          φp.hom.app (tailObject i (le_trans hi₀i₉ hi₉i)) ≫
            φa.hom.app (tailObject i (le_trans hi₀i₉ hi₉i)) =
          φq.hom.app (tailObject i (le_trans hi₀i₉ hi₉i)) ≫
            φb.hom.app (tailObject i (le_trans hi₀i₉ hi₉i))),
        ∀ (i : I) (hi₉i : i₉ ≤ i),
          IsClosedImmersion
            (pullbackComparison φp φq φa φb (tailObject i (le_trans hi₀i₉ hi₉i))
              (comm_stage i hi₉i)) := sorry

end InverseSystemMorphismOverBase

namespace FiniteTypeApproximationLimitSystem

/-- A cartesian square of quasi-separated finite-type algebraic spaces over the
limit of a directed inverse system, presented by finite-type approximation
systems and descended inverse-system morphisms, is eventually stagewise
commutative, and the comparison into the stagewise fibre product is a closed
immersion. -/
@[stacks 0CPF]
theorem exists_eventually_pullback_closedImmersion
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    {i₀ : I}
    {X1sys X2sys X3sys X4sys : Over (OrderDual.toDual i₀) ⥤ AlgebraicSpace S}
    (x1Cone : Cone X1sys) (x2Cone : Cone X2sys)
    (x3Cone : Cone X3sys) (x4Cone : Cone X4sys)
    (x1ToBase : X1sys ⟶ tailBaseDiagram D i₀)
    (x2ToBase : X2sys ⟶ tailBaseDiagram D i₀)
    (x3ToBase : X3sys ⟶ tailBaseDiagram D i₀)
    (x4ToBase : X4sys ⟶ tailBaseDiagram D i₀)
    (x1ToS : x1Cone.pt ⟶ c.pt) (x2ToS : x2Cone.pt ⟶ c.pt)
    (x3ToS : x3Cone.pt ⟶ c.pt) (x4ToS : x4Cone.pt ⟶ c.pt)
    (x1Cone_toBase : ∀ j : Over (OrderDual.toDual i₀),
      x1Cone.π.app j ≫ x1ToBase.app j = x1ToS ≫ c.π.app j.left)
    (x2Cone_toBase : ∀ j : Over (OrderDual.toDual i₀),
      x2Cone.π.app j ≫ x2ToBase.app j = x2ToS ≫ c.π.app j.left)
    (x3Cone_toBase : ∀ j : Over (OrderDual.toDual i₀),
      x3Cone.π.app j ≫ x3ToBase.app j = x3ToS ≫ c.π.app j.left)
    (x4Cone_toBase : ∀ j : Over (OrderDual.toDual i₀),
      x4Cone.π.app j ≫ x4ToBase.app j = x4ToS ≫ c.π.app j.left)
    [QuasiSeparated x1ToS] [FiniteType x1ToS]
    [QuasiSeparated x2ToS] [FiniteType x2ToS]
    [QuasiSeparated x3ToS] [FiniteType x3ToS]
    [QuasiSeparated x4ToS] [FiniteType x4ToS]
    (X1approx : FiniteTypeApproximationLimitSystem D c i₀ X1sys x1Cone x1ToS)
    (X2approx : FiniteTypeApproximationLimitSystem D c i₀ X2sys x2Cone x2ToS)
    (X3approx : FiniteTypeApproximationLimitSystem D c i₀ X3sys x3Cone x3ToS)
    (X4approx : FiniteTypeApproximationLimitSystem D c i₀ X4sys x4Cone x4ToS)
    (φp : InverseSystemMorphismOverBase D i₀ X1sys X3sys x1ToBase x3ToBase)
    (φq : InverseSystemMorphismOverBase D i₀ X1sys X2sys x1ToBase x2ToBase)
    (φa : InverseSystemMorphismOverBase D i₀ X3sys X4sys x3ToBase x4ToBase)
    (φb : InverseSystemMorphismOverBase D i₀ X2sys X4sys x2ToBase x4ToBase)
    (p : x1Cone.pt ⟶ x3Cone.pt) (q : x1Cone.pt ⟶ x2Cone.pt)
    (a : x3Cone.pt ⟶ x4Cone.pt) (b : x2Cone.pt ⟶ x4Cone.pt)
    (hp_overS : p ≫ x3ToS = x1ToS) (hq_overS : q ≫ x2ToS = x1ToS)
    (ha_overS : a ≫ x4ToS = x3ToS) (hb_overS : b ≫ x4ToS = x2ToS)
    (hp_limit : φp.IsLimitMorphism x1Cone x3Cone p)
    (hq_limit : φq.IsLimitMorphism x1Cone x2Cone q)
    (ha_limit : φa.IsLimitMorphism x3Cone x4Cone a)
    (hb_limit : φb.IsLimitMorphism x2Cone x4Cone b)
    (hcart : IsPullback p q a b) :
    ∃ (i₉ : I) (hi₀i₉ : i₀ ≤ i₉),
      InverseSystemMorphismOverBase.PullbackClosedImmersionAt hi₀i₉ φp φq φa φb := sorry

/-- A cartesian square `IsPullback p q a b` of quasi-separated finite-type
algebraic spaces over the limit of a directed inverse system, presented by
finite-type approximation systems and descended inverse-system morphisms, has
an eventually commutative stagewise square whose canonical fibre-product
comparison is an isomorphism when `a` and `b` are flat of finite presentation. -/
@[stacks 0CPF]
theorem exists_eventually_pullback_isIso
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    {i₀ : I}
    {X1sys X2sys X3sys X4sys : Over (OrderDual.toDual i₀) ⥤ AlgebraicSpace S}
    (x1Cone : Cone X1sys) (x2Cone : Cone X2sys)
    (x3Cone : Cone X3sys) (x4Cone : Cone X4sys)
    (x1ToBase : X1sys ⟶ tailBaseDiagram D i₀)
    (x2ToBase : X2sys ⟶ tailBaseDiagram D i₀)
    (x3ToBase : X3sys ⟶ tailBaseDiagram D i₀)
    (x4ToBase : X4sys ⟶ tailBaseDiagram D i₀)
    (x1ToS : x1Cone.pt ⟶ c.pt) (x2ToS : x2Cone.pt ⟶ c.pt)
    (x3ToS : x3Cone.pt ⟶ c.pt) (x4ToS : x4Cone.pt ⟶ c.pt)
    (x1Cone_toBase : ∀ j : Over (OrderDual.toDual i₀),
      x1Cone.π.app j ≫ x1ToBase.app j = x1ToS ≫ c.π.app j.left)
    (x2Cone_toBase : ∀ j : Over (OrderDual.toDual i₀),
      x2Cone.π.app j ≫ x2ToBase.app j = x2ToS ≫ c.π.app j.left)
    (x3Cone_toBase : ∀ j : Over (OrderDual.toDual i₀),
      x3Cone.π.app j ≫ x3ToBase.app j = x3ToS ≫ c.π.app j.left)
    (x4Cone_toBase : ∀ j : Over (OrderDual.toDual i₀),
      x4Cone.π.app j ≫ x4ToBase.app j = x4ToS ≫ c.π.app j.left)
    [QuasiSeparated x1ToS] [FiniteType x1ToS]
    [QuasiSeparated x2ToS] [FiniteType x2ToS]
    [QuasiSeparated x3ToS] [FiniteType x3ToS]
    [QuasiSeparated x4ToS] [FiniteType x4ToS]
    (X1approx : FiniteTypeApproximationLimitSystem D c i₀ X1sys x1Cone x1ToS)
    (X2approx : FiniteTypeApproximationLimitSystem D c i₀ X2sys x2Cone x2ToS)
    (X3approx : FiniteTypeApproximationLimitSystem D c i₀ X3sys x3Cone x3ToS)
    (X4approx : FiniteTypeApproximationLimitSystem D c i₀ X4sys x4Cone x4ToS)
    (φp : InverseSystemMorphismOverBase D i₀ X1sys X3sys x1ToBase x3ToBase)
    (φq : InverseSystemMorphismOverBase D i₀ X1sys X2sys x1ToBase x2ToBase)
    (φa : InverseSystemMorphismOverBase D i₀ X3sys X4sys x3ToBase x4ToBase)
    (φb : InverseSystemMorphismOverBase D i₀ X2sys X4sys x2ToBase x4ToBase)
    (p : x1Cone.pt ⟶ x3Cone.pt) (q : x1Cone.pt ⟶ x2Cone.pt)
    (a : x3Cone.pt ⟶ x4Cone.pt) (b : x2Cone.pt ⟶ x4Cone.pt)
    (hp_overS : p ≫ x3ToS = x1ToS) (hq_overS : q ≫ x2ToS = x1ToS)
    (ha_overS : a ≫ x4ToS = x3ToS) (hb_overS : b ≫ x4ToS = x2ToS)
    (hp_limit : φp.IsLimitMorphism x1Cone x3Cone p)
    (hq_limit : φq.IsLimitMorphism x1Cone x2Cone q)
    (ha_limit : φa.IsLimitMorphism x3Cone x4Cone a)
    (hb_limit : φb.IsLimitMorphism x2Cone x4Cone b)
    (hcart : IsPullback p q a b)
    [Flat a] [FinitePresentation a] [Flat b] [FinitePresentation b] :
    ∃ (i₁₀ : I) (hi₀i₁₀ : i₀ ≤ i₁₀)
      (hcomm : ∀ (i : I) (hi₁₀i : i₁₀ ≤ i),
        φp.hom.app (tailObject i (le_trans hi₀i₁₀ hi₁₀i)) ≫
          φa.hom.app (tailObject i (le_trans hi₀i₁₀ hi₁₀i)) =
        φq.hom.app (tailObject i (le_trans hi₀i₁₀ hi₁₀i)) ≫
          φb.hom.app (tailObject i (le_trans hi₀i₁₀ hi₁₀i))),
      ∀ (i : I) (hi₁₀i : i₁₀ ≤ i),
        IsIso (InverseSystemMorphismOverBase.pullbackComparison φp φq φa φb
          (tailObject i (le_trans hi₀i₁₀ hi₁₀i)) (hcomm i hi₁₀i)) := sorry

end FiniteTypeApproximationLimitSystem

end AlgebraicGeometry.AlgebraicSpace
