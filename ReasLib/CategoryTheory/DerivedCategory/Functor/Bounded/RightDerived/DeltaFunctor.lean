/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Comparison
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

/-- The degree `-1` homology of the bounded-below right-derived delta functor
vanishes on degree-zero objects. -/
@[stacks 05TE]
theorem RightDerived.delta_hneg (X : 𝒜) :
    IsZero (((DerivedCategory.homologyFunctor ℬ 0).shift (-1)).obj
      ((RightDerived.delta RF).toFunctor.obj X)) := sorry

end

end Functor

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]
  (RF : DerivedCategory.Plus 𝒜 ⥤ DerivedCategory.Plus ℬ)
  [RF.CommShift ℤ] [RF.IsTriangulated]

/-- Stacks 05TE: the cohomological delta functor formed by the bounded-below
right derived functors of `RF`. -/
@[stacks 05TE]
noncomputable def Functor.RightDerived.cohomological :
    CohomologicalDeltaFunctor 𝒜 ℬ :=
  DeltaFunctor.toCohomologicalDeltaFunctor
    (Functor.RightDerived.delta RF)
    (DerivedCategory.homologyFunctor ℬ 0)
    (Functor.RightDerived.delta_hneg RF)

/-- The degree-`n` component of `Functor.RightDerived.cohomological RF` is
the corresponding bounded-below right derived functor. -/
@[simp, stacks 05TE]
theorem Functor.RightDerived.cohomological_obj (n : ℕ) :
    ((Functor.RightDerived.cohomological RF).F n).obj =
      Functor.RightDerived.degree RF n := sorry

end

end CategoryTheory
