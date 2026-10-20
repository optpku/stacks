/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Linear

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
variable (x : X ⟶ Spec (CommRingCat.of k)) (y : Y ⟶ Spec (CommRingCat.of k))

/-- The `k`-linear structure on ringed-space modules induced by a structure morphism
to `Spec (CommRingCat.of k)`. -/
@[implicit_reducible]
noncomputable def baseLinearRingedSpace (f : X ⟶ Spec (CommRingCat.of k)) :
    Linear k X.toRingedSpace.Modules :=
  Linear.ofRingMorphism
    ((RingedSpace.GlobalSections.centerHom X.toRingedSpace).comp
      (Scheme.Hom.globalSectionsMap f))

/-- The `k`-linear structure on coherent modules induced by a structure morphism
to `Spec (CommRingCat.of k)`. -/
@[implicit_reducible]
noncomputable def baseLinearCoh (f : X ⟶ Spec (CommRingCat.of k)) :
    Linear k (RingedSpace.Coh X.toRingedSpace) :=
  @CategoryTheory.Linear.fullSubcategory _ _ _ k _
    (baseLinearRingedSpace f) (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)

/-- The relative scalar structure on coherent modules is the full-subcategory
structure induced from ringed-space modules. -/
theorem baseLinearCoh_def (f : X ⟶ Spec (CommRingCat.of k)) :
    baseLinearCoh f =
      @CategoryTheory.Linear.fullSubcategory _ _ _ k _
        (baseLinearRingedSpace f)
          (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) := sorry

/-- A functor of coherent modules is linear over chosen maps to the same affine
base when it is additive and linear for the scalar structures induced by those
maps. -/
class LinearOverCoh (F : RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace) :
    Prop
    extends F.Additive,
      @Functor.Linear k _ (RingedSpace.Coh X.toRingedSpace)
        (RingedSpace.Coh Y.toRingedSpace) _ _ _ _ (baseLinearCoh x) (baseLinearCoh y) F

/-- Relative coherence-linearity consists exactly of additivity and linearity for
the two base-induced scalar structures. -/
theorem linearOverCoh_iff
    (F : RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace) :
    LinearOverCoh x y F ↔
      F.Additive ∧
        @Functor.Linear k _ (RingedSpace.Coh X.toRingedSpace)
          (RingedSpace.Coh Y.toRingedSpace) _ _ _ _
            (baseLinearCoh x) (baseLinearCoh y) F := sorry

/-- The identity functor on coherent modules is linear over a fixed affine-base
structure morphism. -/
instance instLinearOverCoh_id : LinearOverCoh x x (𝟭 (RingedSpace.Coh X.toRingedSpace)) :=
  sorry

/-- A `k`-linear functor of coherent modules is exact-linear when it is an exact
functor `RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace`. -/
class ExactLinearOverCoh
    (F : RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace) : Prop
    extends LinearOverCoh x y F where
  exact :
    exactFunctor (RingedSpace.Coh X.toRingedSpace) (RingedSpace.Coh Y.toRingedSpace) F

/-- Exact-linearity on coherent modules is equivalent to relative `k`-linearity
together with exactness. -/
theorem exactLinearOverCoh_iff
    (F : RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace) :
    ExactLinearOverCoh x y F ↔
      LinearOverCoh x y F ∧
        exactFunctor (RingedSpace.Coh X.toRingedSpace)
          (RingedSpace.Coh Y.toRingedSpace) F := sorry

/-- The category of `k`-linear exact functors of coherent modules. -/
abbrev ExactLinearCohFunctor :=
  ObjectProperty.FullSubcategory fun F : RingedSpace.Coh X.toRingedSpace ⥤
    RingedSpace.Coh Y.toRingedSpace ↦ ExactLinearOverCoh x y F

/-- Objects of `ExactLinearCohFunctor` are exact `k`-linear functors of coherent
modules. -/
instance exactLinearCohFunctor_property (F : ExactLinearCohFunctor x y) :
    ExactLinearOverCoh x y F.obj :=
  F.property

end AlgebraicGeometry.Scheme
