/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Degree.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.DeltaFunctor
public import ReasLib.CategoryTheory.Pretriangulated.DeltaFunctor.Composition.Target
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Naturality of Bounded-Below Right-Derived Delta Functors

A shift-compatible transformation between bounded-below right-derived models
acts first on their pretriangulated delta functors and then on the associated
cohomological delta functors.  The component API identifies the latter action
with the existing degreewise action.
-/

open CategoryTheory
open scoped CategoryTheory

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.RightDerived

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

namespace delta

/-- A shift-compatible transformation of bounded-below right-derived models
induces a morphism of their pretriangulated delta functors. -/
@[stacks 05TE "naturality of bounded-below right-derived delta functors"]
noncomputable def map
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    [RF.CommShift ℤ] [RF.IsTriangulated]
    [RG.CommShift ℤ] [RG.IsTriangulated]
    (τ : RF ⟶ RG) [NatTrans.CommShift τ ℤ] :
    RightDerived.delta RF ⟶ RightDerived.delta RG :=
  DeltaFunctor.postcomposeExactFunctor.map
    (DerivedCategory.Plus.ι : DerivedCategory.Plus B ⥤ DerivedCategory B)
    (DeltaFunctor.postcomposeExactFunctor.target.map
      (DerivedCategory.Plus.singleFunctor.delta A) τ)

/-- The component of the induced delta-functor morphism is the image under
the bounded-below inclusion of the corresponding model component. -/
@[simp, stacks 05TE "component of right-derived delta-functor naturality"]
theorem map_app
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    [RF.CommShift ℤ] [RF.IsTriangulated]
    [RG.CommShift ℤ] [RG.IsTriangulated]
    (τ : RF ⟶ RG) [NatTrans.CommShift τ ℤ] (X : A) :
    (map τ).app.app X =
      (DerivedCategory.Plus.ι : DerivedCategory.Plus B ⥤ DerivedCategory B).map
        (τ.app ((DerivedCategory.Plus.singleFunctor A 0).obj X)) := sorry

/-- Naturality of right-derived delta functors preserves identity
transformations. -/
@[simp]
theorem map_id
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    [RF.CommShift ℤ] [RF.IsTriangulated] :
    map (𝟙 RF) = 𝟙 (RightDerived.delta RF) := sorry

/-- Naturality of right-derived delta functors preserves composition. -/
@[simp]
theorem map_comp
    {RF RG RH : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    [RF.CommShift ℤ] [RF.IsTriangulated]
    [RG.CommShift ℤ] [RG.IsTriangulated]
    [RH.CommShift ℤ] [RH.IsTriangulated]
    (τ : RF ⟶ RG) [NatTrans.CommShift τ ℤ]
    (σ : RG ⟶ RH) [NatTrans.CommShift σ ℤ] :
    map (τ ≫ σ) = map τ ≫ map σ := sorry

end delta

namespace cohomological

/-- A shift-compatible transformation of bounded-below right-derived models
induces a morphism of their cohomological delta functors. -/
@[stacks 05TE "naturality of bounded-below right-derived cohomological delta functors"]
noncomputable def map
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    [RF.CommShift ℤ] [RF.IsTriangulated]
    [RG.CommShift ℤ] [RG.IsTriangulated]
    (τ : RF ⟶ RG) [NatTrans.CommShift τ ℤ] :
    CohomologicalDeltaFunctor.Hom (RightDerived.cohomological RF) (RightDerived.cohomological RG) :=
  DeltaFunctor.toCohomologicalDeltaFunctor.map
    (DerivedCategory.homologyFunctor B 0) (delta.map τ)
    (RightDerived.delta_hneg RF) (RightDerived.delta_hneg RG)

/-- In degree `n`, the induced cohomological morphism is homology applied to
the induced morphism of pretriangulated delta functors. -/
@[simp]
theorem map_app
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    [RF.CommShift ℤ] [RF.IsTriangulated]
    [RG.CommShift ℤ] [RG.IsTriangulated]
    (τ : RF ⟶ RG) [NatTrans.CommShift τ ℤ] (n : ℕ) :
    (map τ).app n = Functor.whiskerRight (delta.map τ).app
      ((DerivedCategory.homologyFunctor B 0).shift (n : ℤ)) := sorry

/-- The degree-`n` component of cohomological naturality is the canonical
degreewise map of the bounded-below right-derived models. -/
@[stacks 015A "cohomological naturality agrees with right-derived degree naturality"]
theorem map_app_eq_degree
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    [RF.CommShift ℤ] [RF.IsTriangulated]
    [RG.CommShift ℤ] [RG.IsTriangulated]
    (τ : RF ⟶ RG) [NatTrans.CommShift τ ℤ] (n : ℕ) :
    (map τ).app n = RightDerived.degree.map τ (n : ℤ) := sorry

/-- Naturality of right-derived cohomological delta functors preserves
identity transformations. -/
@[simp]
theorem map_id
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    [RF.CommShift ℤ] [RF.IsTriangulated] :
    map (𝟙 RF) = CohomologicalDeltaFunctor.Hom.id (RightDerived.cohomological RF) := sorry

/-- Naturality of right-derived cohomological delta functors preserves
composition. -/
@[simp]
theorem map_comp
    {RF RG RH : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    [RF.CommShift ℤ] [RF.IsTriangulated]
    [RG.CommShift ℤ] [RG.IsTriangulated]
    [RH.CommShift ℤ] [RH.IsTriangulated]
    (τ : RF ⟶ RG) [NatTrans.CommShift τ ℤ]
    (σ : RG ⟶ RH) [NatTrans.CommShift σ ℤ] :
    map (τ ≫ σ) = CohomologicalDeltaFunctor.Hom.comp (map τ) (map σ) := sorry

end cohomological

end CategoryTheory.Functor.RightDerived
