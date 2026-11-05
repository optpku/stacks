/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Properties
public import ReasLib.CategoryTheory.Pretriangulated.DeltaFunctor.Cohomological.Naturality
public import ReasLib.CategoryTheory.Pretriangulated.DeltaFunctor.Composition
public import ReasLib.CategoryTheory.Pretriangulated.DeltaFunctor.Transport
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Delta Functors for Bounded-Below Right Derived Functors

This leaf turns the localization-model degree-zero embedding into a
pretriangulated delta functor and then into the cohomological delta functor
whose degree-`n` term is the bounded-below right derived functor.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open ComplexShape
open scoped CategoryTheory

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace DerivedCategory.Plus.singleFunctor.fromHomotopy

section

variable (𝒜 : Type u₁) [Category.{v₁} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- The delta functor on degree-zero objects whose underlying functor is the
localization-model embedding `singleFunctor.fromHomotopy 𝒜 0`. -/
@[stacks 05TE]
noncomputable def delta :
    DeltaFunctor 𝒜 (DerivedCategory.Plus 𝒜) where
  toFunctor := fromHomotopy 𝒜 0
  additive := inferInstance
  δ := fun {S} hS ↦
    ObjectProperty.homMk
      ((compInclusionIso 𝒜 0).hom.app S.X₃ ≫ hS.singleδ ≫
        ((compInclusionIso 𝒜 0).inv.app S.X₁)⟦(1 : ℤ)⟧' ≫
          ((DerivedCategory.Plus.ι : DerivedCategory.Plus 𝒜 ⥤ DerivedCategory 𝒜).commShiftIso
            (1 : ℤ)).inv.app
            ((fromHomotopy 𝒜 0).obj S.X₁))
  map_distinguished := sorry
  δ_naturality := sorry

/-- The underlying functor of `singleFunctor.fromHomotopy.delta` is the
localization-model degree-zero embedding. -/
@[simp]
theorem delta_toFunctor :
    (delta 𝒜).toFunctor = fromHomotopy 𝒜 0 := sorry

end

end DerivedCategory.Plus.singleFunctor.fromHomotopy

namespace DerivedCategory.Plus.singleFunctor

variable (𝒜 : Type u₁) [Category.{v₁} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- The canonical delta functor on Mathlib's bounded-below degree-zero single functor. -/
@[stacks 05TE]
noncomputable def delta :
    DeltaFunctor 𝒜 (DerivedCategory.Plus 𝒜) :=
  (fromHomotopy.delta 𝒜).transport (fromHomotopy.iso 𝒜 0)

/-- The underlying functor of the canonical bounded-below delta functor is Mathlib's
degree-zero single functor. -/
@[simp, stacks 05TE "bounded-below single delta computation"]
theorem delta_toFunctor :
    (delta 𝒜).toFunctor = DerivedCategory.Plus.singleFunctor 𝒜 0 := sorry

end DerivedCategory.Plus.singleFunctor

namespace Functor

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]
  (RF : DerivedCategory.Plus 𝒜 ⥤ DerivedCategory.Plus ℬ)
  [RF.CommShift ℤ] [RF.IsTriangulated]

/-- The pretriangulated delta functor underlying the bounded-below right
derived cohomological delta functor. -/
@[stacks 05TE]
noncomputable def RightDerived.delta :
    DeltaFunctor 𝒜 (DerivedCategory ℬ) :=
  ((DerivedCategory.Plus.singleFunctor.delta 𝒜).postcomposeExactFunctor
    RF).postcomposeExactFunctor (DerivedCategory.Plus.ι : DerivedCategory.Plus ℬ ⥤ DerivedCategory ℬ)

/-- A structural specialization for an exact functor whose degree-zero
images lie in the nonnegative part of the canonical t-structure. This API
is separate from the actual right-derived-model construction below. -/
noncomputable def RightDerived.cohomologicalOfNonnegative
    (h : ∀ X : 𝒜, (RF.obj ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj X)).IsGE 0) :
    CohomologicalDeltaFunctor 𝒜 ℬ :=
  DeltaFunctor.toCohomologicalDeltaFunctor
    (RightDerived.delta RF) (DerivedCategory.homologyFunctor ℬ 0) (fun X ↦ by
      letI := h X
      change IsZero ((DerivedCategory.Plus.homologyFunctor ℬ (-1)).obj
        (RF.obj ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj X)))
      exact DerivedCategory.Plus.isZero_homology_of_isGE _ 0 (-1) (by decide))

/-- The degree `-1` homology of the bounded-below right-derived delta functor
vanishes on degree-zero objects. -/
@[stacks 05TE]
theorem RightDerived.delta_hneg
    (F : 𝒜 ⥤ ℬ) [F.Additive]
    (α : F.toBoundedBelowDerived ⟶ DerivedCategory.Plus.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso 𝒜)] (X : 𝒜) :
    IsZero (((DerivedCategory.homologyFunctor ℬ 0).shift (-1)).obj
      ((RightDerived.delta RF).toFunctor.obj X)) := by
  change IsZero ((RightDerived.degree RF (-1)).obj X)
  exact (RightDerived.degree.isZero_of_neg F RF α (-1) (by decide)).obj X

end

end Functor

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]
  (RF : DerivedCategory.Plus 𝒜 ⥤ DerivedCategory.Plus ℬ)
  [RF.CommShift ℤ] [RF.IsTriangulated]

variable (F : 𝒜 ⥤ ℬ) [F.Additive]
  (α : F.toBoundedBelowDerived ⟶ DerivedCategory.Plus.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso 𝒜)]

/-- Stacks 05TE: the cohomological delta functor formed by the bounded-below
right derived functors of `RF`. -/
@[stacks 05TE]
noncomputable def Functor.RightDerived.cohomological :
    CohomologicalDeltaFunctor 𝒜 ℬ :=
  DeltaFunctor.toCohomologicalDeltaFunctor
    (Functor.RightDerived.delta RF)
    (DerivedCategory.homologyFunctor ℬ 0)
    (Functor.RightDerived.delta_hneg RF F α)

/-- The degree-`n` component of `Functor.RightDerived.cohomological RF` is
the corresponding bounded-below right derived functor. -/
@[simp, stacks 05TE]
theorem Functor.RightDerived.cohomological_obj (n : ℕ) :
    ((Functor.RightDerived.cohomological RF F α).F n).obj =
      Functor.RightDerived.degree RF n := rfl

end

namespace Functor.RightDerived.Bounded

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

/-- Stacks 05TE (1) for an additive functor with an everywhere defined
canonical right-derived functor. No left exactness of `F` is required. -/
@[stacks 05TE]
noncomputable abbrev cohomological
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso 𝒜)]
    [(functor F).CommShift ℤ] [(functor F).IsTriangulated] :
    CohomologicalDeltaFunctor 𝒜 ℬ :=
  RightDerived.cohomological (functor F) F (unit F)

/-- The source-facing 05TE specialization: an additive functor whose
right-derived functor is everywhere defined has a canonical cohomological
delta functor. Shift and triangle structure come from total derivation. -/
@[stacks 05TE "everywhere-defined additive source specialization"]
noncomputable abbrev cohomologicalOfEverywhereDefined
    [Functor.RightDerived.EverywhereDefined F.toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso 𝒜)] :
    CohomologicalDeltaFunctor 𝒜 ℬ :=
  cohomological F

end Functor.RightDerived.Bounded

end CategoryTheory
