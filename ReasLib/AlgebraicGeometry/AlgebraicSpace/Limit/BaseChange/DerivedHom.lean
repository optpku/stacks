/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.HomDiagram
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffine

/-!
# Hom diagrams for base-changed qcqs affine limits of algebraic spaces

This module constructs the stage and limiting derived pullbacks, together with the
canonical filtered diagram of their Hom types.
-/

public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffineLimit

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S}
variable [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsQuasiSeparated (D.obj i)]
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]

/-- The pullback object over `X₀` at a stage of the cofinal tail. -/
private noncomputable abbrev stageOver
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) : Over X₀ :=
  (Over.post D ⋙ Over.pullback x₀).obj j.unop

/-- The canonical projection from a base-changed stage to `X₀`. -/
private noncomputable abbrev stageProjection
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    (baseChangeOverDiagram D (OrderDual.toDual s.base) x₀).obj j.unop ⟶ X₀ :=
  (stageOver s x₀ j).hom

/-- The morphism over `X₀` associated to a transition in the opposite cofinal tail. -/
private noncomputable abbrev stageTransition
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    {j k : (Over (OrderDual.toDual s.base))ᵒᵖ} (f : j ⟶ k) :
    stageOver s x₀ k ⟶ stageOver s x₀ j :=
  (Over.post D ⋙ Over.pullback x₀).map f.unop

/-- The pullback of the limiting cone point, regarded as an object over `X₀`. -/
private noncomputable abbrev limitOver
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base)) : Over X₀ :=
  (Over.pullback x₀).obj
    (Over.mk (s.limitCone.cone.π.app (OrderDual.toDual s.base)))

/-- The canonical projection from the base-changed limit to `X₀`. -/
private noncomputable abbrev limitProjection
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base)) :
    (baseChangeOverCone D s.limitCone.cone (OrderDual.toDual s.base) x₀).pt ⟶ X₀ :=
  (limitOver s x₀).hom

/-- The cone morphism over `X₀` from the base-changed limit to a stage. -/
private noncomputable abbrev limitTransition
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    limitOver s x₀ ⟶ stageOver s x₀ j :=
  ((Over.pullback x₀).mapCone
    ((Over.conePost D (OrderDual.toDual s.base)).obj s.limitCone.cone)).π.app j.unop

/-- Derived pullback from `D(𝒪_{X₀})` to a stage in the base-changed cofinal tail. -/
noncomputable def stagePullback
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    ModuleDerived X₀ ⥤
      ModuleDerived ((baseChangeOverDiagram D (OrderDual.toDual s.base) x₀).obj j.unop) :=
  ModuleDerived.pullback (stageProjection s x₀ j)

/-- `stagePullback` is derived pullback along the canonical projection of the base-changed
stage to `X₀`. -/
theorem stagePullback_eq
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    s.stagePullback x₀ j =
      ModuleDerived.pullback ((Over.post D ⋙ Over.pullback x₀).obj j.unop).hom := sorry

/-- Derived pullback from `D(𝒪_{X₀})` to the base-changed limit. -/
noncomputable def limitPullback
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base)) :
    ModuleDerived X₀ ⥤
      ModuleDerived
        (baseChangeOverCone D s.limitCone.cone (OrderDual.toDual s.base) x₀).pt :=
  ModuleDerived.pullback (limitProjection s x₀)

/-- `limitPullback` is derived pullback along the canonical projection of the base-changed
limit to `X₀`. -/
theorem limitPullback_eq
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base)) :
    s.limitPullback x₀ =
      ModuleDerived.pullback
        ((Over.pullback x₀).obj
          (Over.mk (s.limitCone.cone.π.app (OrderDual.toDual s.base)))).hom := sorry

/-- Derived pullback along a transition followed by the stage projection agrees with the
direct stage pullback from `X₀`. -/
private theorem stagePullback_comp_eq
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    {j k : (Over (OrderDual.toDual s.base))ᵒᵖ} (f : j ⟶ k) :
    ModuleDerived.pullback
        ((stageTransition s x₀ f).left ≫ stageProjection s x₀ j) =
      s.stagePullback x₀ k := sorry

/-- Derived pullback along the limit transition followed by the stage projection agrees with
direct pullback from `X₀` to the base-changed limit. -/
private theorem limitPullback_comp_eq
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    ModuleDerived.pullback
        ((limitTransition s x₀ j).left ≫ stageProjection s x₀ j) =
      s.limitPullback x₀ := sorry

/-- Canonical comparison between iterated pullback along a stage transition and direct
pullback from `X₀` to the later stage. -/
private noncomputable def stagePullbackCompIso
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    {j k : (Over (OrderDual.toDual s.base))ᵒᵖ} (f : j ⟶ k) :
    s.stagePullback x₀ j ⋙ ModuleDerived.pullback (stageTransition s x₀ f).left ≅
      s.stagePullback x₀ k :=
  ModuleDerived.pullbackCompIso
      (stageTransition s x₀ f).left (stageProjection s x₀ j) ≪≫
    eqToIso (stagePullback_comp_eq s x₀ f)

/-- Canonical comparison between pullback through a stage and direct pullback from `X₀`
to the base-changed limit. -/
private noncomputable def limitPullbackCompIso
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    s.stagePullback x₀ j ⋙ ModuleDerived.pullback (limitTransition s x₀ j).left ≅
      s.limitPullback x₀ :=
  ModuleDerived.pullbackCompIso
      (limitTransition s x₀ j).left (stageProjection s x₀ j) ≪≫
    eqToIso (limitPullback_comp_eq s x₀ j)

/-- Pull a morphism between stage derived pullbacks along a transition in the cofinal tail. -/
noncomputable def stageHomMap
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (K₀ L₀ : ModuleDerived X₀)
    {j k : (Over (OrderDual.toDual s.base))ᵒᵖ} (f : j ⟶ k) :
    ((s.stagePullback x₀ j).obj K₀ ⟶ (s.stagePullback x₀ j).obj L₀) →
      ((s.stagePullback x₀ k).obj K₀ ⟶ (s.stagePullback x₀ k).obj L₀) :=
  fun β ↦
    (stagePullbackCompIso s x₀ f).inv.app K₀ ≫
      (ModuleDerived.pullback (stageTransition s x₀ f).left).map β ≫
      (stagePullbackCompIso s x₀ f).hom.app L₀

/-- The stage Hom transition associated to an identity is the identity function. -/
theorem stageHomMap_id
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (K₀ L₀ : ModuleDerived X₀)
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    s.stageHomMap x₀ K₀ L₀ (𝟙 j) =
      𝟙 ((s.stagePullback x₀ j).obj K₀ ⟶ (s.stagePullback x₀ j).obj L₀) := sorry

/-- Stage Hom transitions respect composition. -/
theorem stageHomMap_comp
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (K₀ L₀ : ModuleDerived X₀)
    {j k l : (Over (OrderDual.toDual s.base))ᵒᵖ} (f : j ⟶ k) (g : k ⟶ l) :
    s.stageHomMap x₀ K₀ L₀ (f ≫ g) =
      Function.comp (s.stageHomMap x₀ K₀ L₀ g) (s.stageHomMap x₀ K₀ L₀ f) := sorry

/-- The stage Hom identity map is the identity morphism of its Hom type. -/
private theorem stageHomMap_id_cat
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (K₀ L₀ : ModuleDerived X₀)
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    TypeCat.ofHom (s.stageHomMap x₀ K₀ L₀ (𝟙 j)) = 𝟙 _ := sorry

/-- The categorical stage Hom maps respect composition. -/
private theorem stageHomMap_comp_cat
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (K₀ L₀ : ModuleDerived X₀)
    {j k l : (Over (OrderDual.toDual s.base))ᵒᵖ} (f : j ⟶ k) (g : k ⟶ l) :
    TypeCat.ofHom (s.stageHomMap x₀ K₀ L₀ (f ≫ g)) =
      TypeCat.ofHom
        (Function.comp (s.stageHomMap x₀ K₀ L₀ g) (s.stageHomMap x₀ K₀ L₀ f)) := sorry

/-- The concrete functor of Hom types between the stage derived pullbacks. -/
@[expose]
noncomputable def stageHomFunctor
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (K₀ L₀ : ModuleDerived X₀) :
    (Over (OrderDual.toDual s.base))ᵒᵖ ⥤ Type _ where
  obj j := (s.stagePullback x₀ j).obj K₀ ⟶ (s.stagePullback x₀ j).obj L₀
  map f := TypeCat.ofHom (s.stageHomMap x₀ K₀ L₀ f)
  map_id j := private stageHomMap_id_cat s x₀ K₀ L₀ j
  map_comp f g := private stageHomMap_comp_cat s x₀ K₀ L₀ f g

/-- The object value of the stage Hom functor is the expected derived-category Hom type. -/
theorem stageHomFunctor_obj
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (K₀ L₀ : ModuleDerived X₀)
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    (s.stageHomFunctor x₀ K₀ L₀).obj j =
      ((s.stagePullback x₀ j).obj K₀ ⟶ (s.stagePullback x₀ j).obj L₀) := sorry

/-- The map of the stage Hom functor is the canonical pullback transition. -/
theorem stageHomFunctor_map
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (K₀ L₀ : ModuleDerived X₀)
    {j k : (Over (OrderDual.toDual s.base))ᵒᵖ} (f : j ⟶ k) :
    (s.stageHomFunctor x₀ K₀ L₀).map f = TypeCat.ofHom (s.stageHomMap x₀ K₀ L₀ f) := sorry

/-- Pull a stage morphism to the base-changed limit along its cone projection. -/
noncomputable def stageToLimitHom
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (K₀ L₀ : ModuleDerived X₀)
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    ((s.stagePullback x₀ j).obj K₀ ⟶ (s.stagePullback x₀ j).obj L₀) →
      ((s.limitPullback x₀).obj K₀ ⟶ (s.limitPullback x₀).obj L₀) :=
  fun β ↦
    (limitPullbackCompIso s x₀ j).inv.app K₀ ≫
      (ModuleDerived.pullback (limitTransition s x₀ j).left).map β ≫
      (limitPullbackCompIso s x₀ j).hom.app L₀

/-- The stage-to-limit Hom maps commute with the transition maps. -/
theorem stageToLimitHom_natural
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (K₀ L₀ : ModuleDerived X₀)
    {j k : (Over (OrderDual.toDual s.base))ᵒᵖ} (f : j ⟶ k)
    (β : (s.stageHomFunctor x₀ K₀ L₀).obj j) :
    s.stageToLimitHom x₀ K₀ L₀ k ((s.stageHomFunctor x₀ K₀ L₀).map f β) =
      s.stageToLimitHom x₀ K₀ L₀ j β := sorry

/-- The canonical filtered Hom diagram for the base-changed tail and its limit. -/
noncomputable def homDiagram
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (K₀ L₀ : ModuleDerived X₀) :
    DerivedCategory.FilteredColimit.HomDiagram
      (s.stageHomFunctor x₀ K₀ L₀)
      ((s.limitPullback x₀).obj K₀ ⟶ (s.limitPullback x₀).obj L₀) :=
  { ι := s.stageToLimitHom x₀ K₀ L₀
    natural := fun {_ _} f β ↦ s.stageToLimitHom_natural x₀ K₀ L₀ f β }

/-- Each cocone leg of `homDiagram` is the canonical stage-to-limit Hom map. -/
theorem homDiagram_ι
    (s : QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (K₀ L₀ : ModuleDerived X₀)
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    (s.homDiagram x₀ K₀ L₀).ι j = s.stageToLimitHom x₀ K₀ L₀ j := sorry

end AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffineLimit
