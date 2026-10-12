/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.HomDiagram
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Limit.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Limit.QcqsAffine

public section

/-!
# Hom diagrams for base-changed qcqs affine limits

This module constructs the stage and limiting derived pullbacks, together with the
canonical filtered diagram of their Hom types.
-/

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Limit.QcqsAffineLimit

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {D : OrderDual I ⥤ Scheme.{u}}
variable [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
variable [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]

/-- The pullback object over `X₀` at a stage of the cofinal tail. -/
private noncomputable abbrev stageOver
    (s : Scheme.Limit.QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) : Over X₀ :=
  (Over.post D ⋙ Over.pullback x₀).obj j.unop

/-- The canonical projection from a base-changed stage to `X₀`. -/
private noncomputable abbrev stageProjection
    (s : Scheme.Limit.QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    (Scheme.baseChangeOverDiagram D (OrderDual.toDual s.base) x₀).obj j.unop ⟶ X₀ :=
  (stageOver s x₀ j).hom

/-- The morphism over `X₀` associated to a transition in the opposite cofinal tail. -/
private noncomputable abbrev stageTransition
    (s : Scheme.Limit.QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    {j k : (Over (OrderDual.toDual s.base))ᵒᵖ} (f : j ⟶ k) :
    stageOver s x₀ k ⟶ stageOver s x₀ j :=
  (Over.post D ⋙ Over.pullback x₀).map f.unop

/-- The pullback of the limiting cone point, regarded as an object over `X₀`. -/
private noncomputable abbrev limitOver
    (s : Scheme.Limit.QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base)) : Over X₀ :=
  (Over.pullback x₀).obj
    (Over.mk (s.limitCone.cone.π.app (OrderDual.toDual s.base)))

/-- The canonical projection from the base-changed limit to `X₀`. -/
private noncomputable abbrev limitProjection
    (s : Scheme.Limit.QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base)) :
    (Scheme.baseChangeOverCone D s.limitCone.cone
      (OrderDual.toDual s.base) x₀).pt ⟶ X₀ :=
  (limitOver s x₀).hom

/-- The cone morphism over `X₀` from the base-changed limit to a stage. -/
private noncomputable abbrev limitTransition
    (s : Scheme.Limit.QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    limitOver s x₀ ⟶ stageOver s x₀ j :=
  ((Over.pullback x₀).mapCone
    ((Over.conePost D (OrderDual.toDual s.base)).obj s.limitCone.cone)).π.app j.unop

/-- Derived pullback from `D(𝒪_{X₀})` to a stage in the base-changed cofinal tail. -/
noncomputable def stagePullback
    (s : Scheme.Limit.QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    RingedSpace.ModuleDerived X₀.toRingedSpace ⥤
      RingedSpace.ModuleDerived
        ((Scheme.baseChangeOverDiagram D (OrderDual.toDual s.base) x₀).obj
          j.unop).toRingedSpace :=
  RingedSpace.modulePullbackDerived (stageProjection s x₀ j).toLRSHom.toShHom

/-- Derived pullback from `D(𝒪_{X₀})` to the base-changed limit. -/
noncomputable def limitPullback
    (s : Scheme.Limit.QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base)) :
    RingedSpace.ModuleDerived X₀.toRingedSpace ⥤
      RingedSpace.ModuleDerived
        (Scheme.baseChangeOverCone D s.limitCone.cone
          (OrderDual.toDual s.base) x₀).pt.toRingedSpace :=
  RingedSpace.modulePullbackDerived (limitProjection s x₀).toLRSHom.toShHom

/-- Derived pullback along a transition followed by the stage projection agrees with the
direct stage pullback from `X₀`. -/
private theorem stagePullback_comp_eq
    (s : Scheme.Limit.QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    {j k : (Over (OrderDual.toDual s.base))ᵒᵖ} (f : j ⟶ k) :
    RingedSpace.modulePullbackDerived
        ((stageTransition s x₀ f).left.toLRSHom.toShHom ≫
          (stageProjection s x₀ j).toLRSHom.toShHom) =
      s.stagePullback x₀ k := sorry

/-- Derived pullback along the limit transition followed by the stage projection agrees with
direct pullback from `X₀` to the base-changed limit. -/
private theorem limitPullback_comp_eq
    (s : Scheme.Limit.QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    RingedSpace.modulePullbackDerived
        ((limitTransition s x₀ j).left.toLRSHom.toShHom ≫
          (stageProjection s x₀ j).toLRSHom.toShHom) =
      s.limitPullback x₀ := sorry

/-- Canonical comparison between iterated pullback along a stage transition and direct
pullback from `X₀` to the later stage. -/
private noncomputable def stagePullbackCompIso
    (s : Scheme.Limit.QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    {j k : (Over (OrderDual.toDual s.base))ᵒᵖ} (f : j ⟶ k) :
    s.stagePullback x₀ j ⋙
        RingedSpace.modulePullbackDerived
          (stageTransition s x₀ f).left.toLRSHom.toShHom ≅
      s.stagePullback x₀ k :=
  RingedSpace.modulePullbackDerived.compIso
      (stageTransition s x₀ f).left.toLRSHom.toShHom
      (stageProjection s x₀ j).toLRSHom.toShHom
      (RingedSpace.modulePullbackDerived.compComparison_isIso
        (stageTransition s x₀ f).left.toLRSHom.toShHom
        (stageProjection s x₀ j).toLRSHom.toShHom) ≪≫
    eqToIso (stagePullback_comp_eq s x₀ f)

/-- Canonical comparison between pullback through a stage and direct pullback from `X₀`
to the base-changed limit. -/
private noncomputable def limitPullbackCompIso
    (s : Scheme.Limit.QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    s.stagePullback x₀ j ⋙
        RingedSpace.modulePullbackDerived
          (limitTransition s x₀ j).left.toLRSHom.toShHom ≅
      s.limitPullback x₀ :=
  RingedSpace.modulePullbackDerived.compIso
      (limitTransition s x₀ j).left.toLRSHom.toShHom
      (stageProjection s x₀ j).toLRSHom.toShHom
      (RingedSpace.modulePullbackDerived.compComparison_isIso
        (limitTransition s x₀ j).left.toLRSHom.toShHom
        (stageProjection s x₀ j).toLRSHom.toShHom) ≪≫
    eqToIso (limitPullback_comp_eq s x₀ j)

/-- Pull a morphism between stage derived pullbacks along a transition in the cofinal tail. -/
noncomputable def stageHomMap
    (s : Scheme.Limit.QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (K₀ L₀ : RingedSpace.ModuleDerived X₀.toRingedSpace)
    {j k : (Over (OrderDual.toDual s.base))ᵒᵖ} (f : j ⟶ k) :
    ((s.stagePullback x₀ j).obj K₀ ⟶ (s.stagePullback x₀ j).obj L₀) →
      ((s.stagePullback x₀ k).obj K₀ ⟶ (s.stagePullback x₀ k).obj L₀) :=
  fun β ↦
    (stagePullbackCompIso s x₀ f).inv.app K₀ ≫
      (RingedSpace.modulePullbackDerived
        (stageTransition s x₀ f).left.toLRSHom.toShHom).map β ≫
      (stagePullbackCompIso s x₀ f).hom.app L₀

/-- The stage Hom transition associated to an identity is the identity function. -/
theorem stageHomMap_id
    (s : Scheme.Limit.QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (K₀ L₀ : RingedSpace.ModuleDerived X₀.toRingedSpace)
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    s.stageHomMap x₀ K₀ L₀ (𝟙 j) =
      𝟙 ((s.stagePullback x₀ j).obj K₀ ⟶ (s.stagePullback x₀ j).obj L₀) := sorry

/-- Stage Hom transitions respect composition. -/
theorem stageHomMap_comp
    (s : Scheme.Limit.QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (K₀ L₀ : RingedSpace.ModuleDerived X₀.toRingedSpace)
    {j k l : (Over (OrderDual.toDual s.base))ᵒᵖ}
    (f : j ⟶ k) (g : k ⟶ l) :
    s.stageHomMap x₀ K₀ L₀ (f ≫ g) =
      Function.comp (s.stageHomMap x₀ K₀ L₀ g) (s.stageHomMap x₀ K₀ L₀ f) := sorry

/-- The identity law in the categorical `Type` morphism wrapper. -/
theorem stageHomMap_id_cat
    (s : Scheme.Limit.QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (K₀ L₀ : RingedSpace.ModuleDerived X₀.toRingedSpace)
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    TypeCat.ofHom (s.stageHomMap x₀ K₀ L₀ (𝟙 j)) = 𝟙 _ := sorry

/-- The composition law in the categorical `Type` morphism wrapper. -/
theorem stageHomMap_comp_cat
    (s : Scheme.Limit.QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (K₀ L₀ : RingedSpace.ModuleDerived X₀.toRingedSpace)
    {j k l : (Over (OrderDual.toDual s.base))ᵒᵖ}
    (f : j ⟶ k) (g : k ⟶ l) :
    TypeCat.ofHom (s.stageHomMap x₀ K₀ L₀ (f ≫ g)) =
      TypeCat.ofHom
        (Function.comp (s.stageHomMap x₀ K₀ L₀ g) (s.stageHomMap x₀ K₀ L₀ f)) := sorry

/-- The concrete functor of Hom types between the stage derived pullbacks. -/
@[expose]
noncomputable def stageHomFunctor
    (s : Scheme.Limit.QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (K₀ L₀ : RingedSpace.ModuleDerived X₀.toRingedSpace) :
    (Over (OrderDual.toDual s.base))ᵒᵖ ⥤ Type _ where
  obj j := (s.stagePullback x₀ j).obj K₀ ⟶ (s.stagePullback x₀ j).obj L₀
  map f := TypeCat.ofHom (s.stageHomMap x₀ K₀ L₀ f)
  map_id j := s.stageHomMap_id_cat x₀ K₀ L₀ j
  map_comp f g := s.stageHomMap_comp_cat x₀ K₀ L₀ f g

/-- The object value of the stage Hom functor is the expected derived-category Hom type. -/
theorem stageHomFunctor_obj
    (s : Scheme.Limit.QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (K₀ L₀ : RingedSpace.ModuleDerived X₀.toRingedSpace)
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    (s.stageHomFunctor x₀ K₀ L₀).obj j =
      ((s.stagePullback x₀ j).obj K₀ ⟶ (s.stagePullback x₀ j).obj L₀) := sorry

/-- The map of the stage Hom functor is the canonical pullback transition. -/
theorem stageHomFunctor_map
    (s : Scheme.Limit.QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (K₀ L₀ : RingedSpace.ModuleDerived X₀.toRingedSpace)
    {j k : (Over (OrderDual.toDual s.base))ᵒᵖ} (f : j ⟶ k) :
    (s.stageHomFunctor x₀ K₀ L₀).map f =
      TypeCat.ofHom (s.stageHomMap x₀ K₀ L₀ f) := sorry

/-- Pull a stage morphism to the base-changed limit along its cone projection. -/
noncomputable def stageToLimitHom
    (s : Scheme.Limit.QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (K₀ L₀ : RingedSpace.ModuleDerived X₀.toRingedSpace)
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    ((s.stagePullback x₀ j).obj K₀ ⟶ (s.stagePullback x₀ j).obj L₀) →
      ((s.limitPullback x₀).obj K₀ ⟶ (s.limitPullback x₀).obj L₀) :=
  fun β ↦
    (limitPullbackCompIso s x₀ j).inv.app K₀ ≫
      (RingedSpace.modulePullbackDerived
        (limitTransition s x₀ j).left.toLRSHom.toShHom).map β ≫
      (limitPullbackCompIso s x₀ j).hom.app L₀

/-- The stage-to-limit Hom maps commute with the transition maps. -/
theorem stageToLimitHom_natural
    (s : Scheme.Limit.QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (K₀ L₀ : RingedSpace.ModuleDerived X₀.toRingedSpace)
    {j k : (Over (OrderDual.toDual s.base))ᵒᵖ} (f : j ⟶ k)
    (β : (s.stageHomFunctor x₀ K₀ L₀).obj j) :
    s.stageToLimitHom x₀ K₀ L₀ k ((s.stageHomFunctor x₀ K₀ L₀).map f β) =
      s.stageToLimitHom x₀ K₀ L₀ j β := sorry

/-- Naturality in the exact bundled form required by the filtered Hom diagram. -/
private theorem homDiagram_natural
    (s : Scheme.Limit.QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (K₀ L₀ : RingedSpace.ModuleDerived X₀.toRingedSpace) :
    ∀ ⦃j k : (Over (OrderDual.toDual s.base))ᵒᵖ⦄ (f : j ⟶ k)
      (β : (s.stageHomFunctor x₀ K₀ L₀).obj j),
      s.stageToLimitHom x₀ K₀ L₀ k ((s.stageHomFunctor x₀ K₀ L₀).map f β) =
        s.stageToLimitHom x₀ K₀ L₀ j β := sorry

/-- The canonical filtered Hom diagram for the base-changed tail and its limit. -/
noncomputable def homDiagram
    (s : Scheme.Limit.QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (K₀ L₀ : RingedSpace.ModuleDerived X₀.toRingedSpace) :
    DerivedCategory.FilteredColimit.HomDiagram
      (s.stageHomFunctor x₀ K₀ L₀)
      ((s.limitPullback x₀).obj K₀ ⟶ (s.limitPullback x₀).obj L₀) :=
  { ι := s.stageToLimitHom x₀ K₀ L₀
    natural := s.homDiagram_natural x₀ K₀ L₀ }

/-- Each cocone leg of `homDiagram` is the canonical stage-to-limit Hom map. -/
theorem homDiagram_ι
    (s : Scheme.Limit.QcqsAffineLimit D) {X₀ : Scheme.{u}}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    (K₀ L₀ : RingedSpace.ModuleDerived X₀.toRingedSpace)
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    (s.homDiagram x₀ K₀ L₀).ι j = s.stageToLimitHom x₀ K₀ L₀ j := sorry

end AlgebraicGeometry.Scheme.Limit.QcqsAffineLimit
