/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.HomDiagram
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Limit.QcqsAffine

public section

/-!
# Derived Hom diagrams for qcqs affine limits

This module constructs the direct stage and limiting derived pullbacks, together with
the canonical filtered diagram of their Hom types.
-/

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Limit.QcqsAffineLimit.DerivedHom

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {D : OrderDual I ⥤ Scheme.{u}}
variable [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
variable [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]

/-- The projection from a stage in the cofinal tail to the distinguished base stage. -/
private noncomputable abbrev stageProjection
    (s : Scheme.Limit.QcqsAffineLimit D)
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    D.obj j.unop.left ⟶ D.obj (OrderDual.toDual s.base) :=
  D.map j.unop.hom

/-- The transition morphism associated to a morphism in the opposite cofinal tail. -/
private noncomputable abbrev stageTransition
    (s : Scheme.Limit.QcqsAffineLimit D)
    {j k : (Over (OrderDual.toDual s.base))ᵒᵖ} (f : j ⟶ k) :
    D.obj k.unop.left ⟶ D.obj j.unop.left :=
  D.map f.unop.left

/-- The limiting cone projection to the distinguished base stage. -/
private noncomputable abbrev limitProjection
    (s : Scheme.Limit.QcqsAffineLimit D) :
    s.limitCone.cone.pt ⟶ D.obj (OrderDual.toDual s.base) :=
  s.limitCone.cone.π.app (OrderDual.toDual s.base)

/-- Derived pullback from the distinguished stage to a stage in the cofinal tail. -/
noncomputable def stagePullback
    (s : Scheme.Limit.QcqsAffineLimit D)
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    RingedSpace.ModuleDerived (D.obj (OrderDual.toDual s.base)).toRingedSpace ⥤
      RingedSpace.ModuleDerived (D.obj j.unop.left).toRingedSpace :=
  RingedSpace.modulePullbackDerived (stageProjection s j).toLRSHom.toShHom

/-- The value of `stagePullback` is the canonical derived pullback along the stage projection. -/
theorem stagePullback_obj
    (s : Scheme.Limit.QcqsAffineLimit D)
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ)
    (E₀ : RingedSpace.ModuleDerived
      (D.obj (OrderDual.toDual s.base)).toRingedSpace) :
    (stagePullback s j).obj E₀ =
      (RingedSpace.modulePullbackDerived
        (D.map j.unop.hom).toLRSHom.toShHom).obj E₀ := sorry

/-- Derived pullback from the distinguished stage to the specified limiting scheme. -/
noncomputable def limitPullback
    (s : Scheme.Limit.QcqsAffineLimit D) :
    RingedSpace.ModuleDerived (D.obj (OrderDual.toDual s.base)).toRingedSpace ⥤
      RingedSpace.ModuleDerived s.limitCone.cone.pt.toRingedSpace :=
  RingedSpace.modulePullbackDerived (limitProjection s).toLRSHom.toShHom

/-- The value of `limitPullback` is the canonical derived pullback along the limiting
cone projection. -/
theorem limitPullback_obj
    (s : Scheme.Limit.QcqsAffineLimit D)
    (E₀ : RingedSpace.ModuleDerived
      (D.obj (OrderDual.toDual s.base)).toRingedSpace) :
    (limitPullback s).obj E₀ =
      (RingedSpace.modulePullbackDerived
        (s.limitCone.cone.π.app
          (OrderDual.toDual s.base)).toLRSHom.toShHom).obj E₀ := sorry

/-- Derived pullback along a transition followed by the stage projection agrees with
direct pullback from the distinguished stage. -/
private theorem stagePullback_comp_eq
    (s : Scheme.Limit.QcqsAffineLimit D)
    {j k : (Over (OrderDual.toDual s.base))ᵒᵖ} (f : j ⟶ k) :
    RingedSpace.modulePullbackDerived
        ((stageTransition s f).toLRSHom.toShHom ≫
          (stageProjection s j).toLRSHom.toShHom) =
      stagePullback s k := sorry

/-- Derived pullback through a stage agrees with direct pullback to the limit. -/
private theorem limitPullback_comp_eq
    (s : Scheme.Limit.QcqsAffineLimit D)
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    RingedSpace.modulePullbackDerived
        ((s.limitCone.cone.π.app j.unop.left).toLRSHom.toShHom ≫
          (stageProjection s j).toLRSHom.toShHom) =
      limitPullback s := sorry

/-- The canonical comparison between iterated pullback along a stage transition and
direct pullback from the distinguished stage. -/
private noncomputable def stagePullbackCompIso
    (s : Scheme.Limit.QcqsAffineLimit D)
    {j k : (Over (OrderDual.toDual s.base))ᵒᵖ} (f : j ⟶ k) :
    stagePullback s j ⋙
        RingedSpace.modulePullbackDerived
          (stageTransition s f).toLRSHom.toShHom ≅
      stagePullback s k :=
  RingedSpace.modulePullbackDerived.compIso
      (stageTransition s f).toLRSHom.toShHom
      (stageProjection s j).toLRSHom.toShHom
      (RingedSpace.modulePullbackDerived.compComparison_isIso
        (stageTransition s f).toLRSHom.toShHom
        (stageProjection s j).toLRSHom.toShHom) ≪≫
    eqToIso (stagePullback_comp_eq s f)

/-- The canonical comparison between pullback through a stage and direct pullback to
the limiting scheme. -/
private noncomputable def limitPullbackCompIso
    (s : Scheme.Limit.QcqsAffineLimit D)
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    stagePullback s j ⋙
        RingedSpace.modulePullbackDerived
          (s.limitCone.cone.π.app j.unop.left).toLRSHom.toShHom ≅
      limitPullback s :=
  RingedSpace.modulePullbackDerived.compIso
      (s.limitCone.cone.π.app j.unop.left).toLRSHom.toShHom
      (stageProjection s j).toLRSHom.toShHom
      (RingedSpace.modulePullbackDerived.compComparison_isIso
        (s.limitCone.cone.π.app j.unop.left).toLRSHom.toShHom
        (stageProjection s j).toLRSHom.toShHom) ≪≫
    eqToIso (limitPullback_comp_eq s j)

/-- Pull a morphism between stage derived pullbacks along a transition in the cofinal tail. -/
noncomputable def stageHomMap
    (s : Scheme.Limit.QcqsAffineLimit D)
    (E₀ K₀ : RingedSpace.ModuleDerived
      (D.obj (OrderDual.toDual s.base)).toRingedSpace)
    {j k : (Over (OrderDual.toDual s.base))ᵒᵖ} (f : j ⟶ k) :
    ((stagePullback s j).obj E₀ ⟶ (stagePullback s j).obj K₀) →
      ((stagePullback s k).obj E₀ ⟶ (stagePullback s k).obj K₀) :=
  fun β ↦
    (stagePullbackCompIso s f).inv.app E₀ ≫
      (RingedSpace.modulePullbackDerived
        (stageTransition s f).toLRSHom.toShHom).map β ≫
      (stagePullbackCompIso s f).hom.app K₀

/-- The stage Hom transition associated to an identity is the identity function. -/
theorem stageHomMap_id
    (s : Scheme.Limit.QcqsAffineLimit D)
    (E₀ K₀ : RingedSpace.ModuleDerived
      (D.obj (OrderDual.toDual s.base)).toRingedSpace)
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    stageHomMap s E₀ K₀ (𝟙 j) =
      𝟙 ((stagePullback s j).obj E₀ ⟶ (stagePullback s j).obj K₀) := sorry

/-- Stage Hom transitions respect composition. -/
theorem stageHomMap_comp
    (s : Scheme.Limit.QcqsAffineLimit D)
    (E₀ K₀ : RingedSpace.ModuleDerived
      (D.obj (OrderDual.toDual s.base)).toRingedSpace)
    {j k l : (Over (OrderDual.toDual s.base))ᵒᵖ}
    (f : j ⟶ k) (g : k ⟶ l) :
    stageHomMap s E₀ K₀ (f ≫ g) =
      Function.comp (stageHomMap s E₀ K₀ g) (stageHomMap s E₀ K₀ f) := sorry

/-- The identity law in the categorical `Type` morphism wrapper. -/
theorem stageHomMap_id_cat
    (s : Scheme.Limit.QcqsAffineLimit D)
    (E₀ K₀ : RingedSpace.ModuleDerived
      (D.obj (OrderDual.toDual s.base)).toRingedSpace)
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    TypeCat.ofHom (stageHomMap s E₀ K₀ (𝟙 j)) = 𝟙 _ := sorry

/-- The composition law in the categorical `Type` morphism wrapper. -/
theorem stageHomMap_comp_cat
    (s : Scheme.Limit.QcqsAffineLimit D)
    (E₀ K₀ : RingedSpace.ModuleDerived
      (D.obj (OrderDual.toDual s.base)).toRingedSpace)
    {j k l : (Over (OrderDual.toDual s.base))ᵒᵖ}
    (f : j ⟶ k) (g : k ⟶ l) :
    TypeCat.ofHom (stageHomMap s E₀ K₀ (f ≫ g)) =
      TypeCat.ofHom
        (Function.comp (stageHomMap s E₀ K₀ g) (stageHomMap s E₀ K₀ f)) := sorry

/-- The concrete functor of Hom types between the direct stage derived pullbacks. -/
@[expose]
noncomputable def stageFunctor
    (s : Scheme.Limit.QcqsAffineLimit D)
    (E₀ K₀ : RingedSpace.ModuleDerived
      (D.obj (OrderDual.toDual s.base)).toRingedSpace) :
    (Over (OrderDual.toDual s.base))ᵒᵖ ⥤ Type _ where
  obj j := (stagePullback s j).obj E₀ ⟶ (stagePullback s j).obj K₀
  map f := TypeCat.ofHom (stageHomMap s E₀ K₀ f)
  map_id j := stageHomMap_id_cat s E₀ K₀ j
  map_comp f g := stageHomMap_comp_cat s E₀ K₀ f g

/-- The object value of the stage functor is the expected derived-category Hom type. -/
theorem stageFunctor_obj
    (s : Scheme.Limit.QcqsAffineLimit D)
    (E₀ K₀ : RingedSpace.ModuleDerived
      (D.obj (OrderDual.toDual s.base)).toRingedSpace)
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    (stageFunctor s E₀ K₀).obj j =
      ((stagePullback s j).obj E₀ ⟶ (stagePullback s j).obj K₀) := sorry

/-- The map of the stage functor is the canonical derived-pullback transition. -/
theorem stageFunctor_map
    (s : Scheme.Limit.QcqsAffineLimit D)
    (E₀ K₀ : RingedSpace.ModuleDerived
      (D.obj (OrderDual.toDual s.base)).toRingedSpace)
    {j k : (Over (OrderDual.toDual s.base))ᵒᵖ} (f : j ⟶ k) :
    (stageFunctor s E₀ K₀).map f =
      TypeCat.ofHom (stageHomMap s E₀ K₀ f) := sorry

/-- Pull a stage morphism to the limiting scheme along the corresponding cone projection. -/
noncomputable def stageToLimit
    (s : Scheme.Limit.QcqsAffineLimit D)
    (E₀ K₀ : RingedSpace.ModuleDerived
      (D.obj (OrderDual.toDual s.base)).toRingedSpace)
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    ((stagePullback s j).obj E₀ ⟶ (stagePullback s j).obj K₀) →
      ((limitPullback s).obj E₀ ⟶ (limitPullback s).obj K₀) :=
  fun β ↦
    (limitPullbackCompIso s j).inv.app E₀ ≫
      (RingedSpace.modulePullbackDerived
        (s.limitCone.cone.π.app j.unop.left).toLRSHom.toShHom).map β ≫
      (limitPullbackCompIso s j).hom.app K₀

/-- The stage-to-limit Hom maps commute with the transition maps. -/
theorem stageToLimit_natural
    (s : Scheme.Limit.QcqsAffineLimit D)
    (E₀ K₀ : RingedSpace.ModuleDerived
      (D.obj (OrderDual.toDual s.base)).toRingedSpace)
    {j k : (Over (OrderDual.toDual s.base))ᵒᵖ} (f : j ⟶ k)
    (β : (stageFunctor s E₀ K₀).obj j) :
    stageToLimit s E₀ K₀ k ((stageFunctor s E₀ K₀).map f β) =
      stageToLimit s E₀ K₀ j β := sorry

/-- Naturality in the bundled form required by the filtered Hom diagram. -/
theorem diagram_natural
    (s : Scheme.Limit.QcqsAffineLimit D)
    (E₀ K₀ : RingedSpace.ModuleDerived
      (D.obj (OrderDual.toDual s.base)).toRingedSpace) :
    ∀ ⦃j k : (Over (OrderDual.toDual s.base))ᵒᵖ⦄ (f : j ⟶ k)
      (β : (stageFunctor s E₀ K₀).obj j),
      stageToLimit s E₀ K₀ k ((stageFunctor s E₀ K₀).map f β) =
        stageToLimit s E₀ K₀ j β := sorry

/-- The canonical filtered Hom diagram for the direct cofinal tail and its limit. -/
noncomputable def diagram
    (s : Scheme.Limit.QcqsAffineLimit D)
    (E₀ K₀ : RingedSpace.ModuleDerived
      (D.obj (OrderDual.toDual s.base)).toRingedSpace) :
    DerivedCategory.FilteredColimit.HomDiagram
      (stageFunctor s E₀ K₀)
      ((limitPullback s).obj E₀ ⟶ (limitPullback s).obj K₀) :=
  { ι := stageToLimit s E₀ K₀
    natural := diagram_natural s E₀ K₀ }

/-- Each cocone leg of `diagram` is the canonical stage-to-limit Hom map. -/
theorem diagram_ι
    (s : Scheme.Limit.QcqsAffineLimit D)
    (E₀ K₀ : RingedSpace.ModuleDerived
      (D.obj (OrderDual.toDual s.base)).toRingedSpace)
    (j : (Over (OrderDual.toDual s.base))ᵒᵖ) :
    (diagram s E₀ K₀).ι j = stageToLimit s E₀ K₀ j := sorry

end AlgebraicGeometry.Scheme.Limit.QcqsAffineLimit.DerivedHom
