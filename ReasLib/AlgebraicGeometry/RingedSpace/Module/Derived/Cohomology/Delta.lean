/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Grothendieck
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.Algebra.Homology.HomotopyCategory.QuasiIso
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated
public import ReasLib.CategoryTheory.Pretriangulated.DeltaFunctor.Composition
public import ReasLib.CategoryTheory.Pretriangulated.DeltaFunctor.Cohomological
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Linear
import Mathlib.Tactic.CrossRefAttribute

/-!
# Global cohomology as a cohomological delta functor

The total right-derived global-sections functor and homology define the module-valued
cohomological delta functor of a ringed space.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.CohomologicalDeltaFunctor
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Delta

variable {X : RingedSpace.{u}}

/-- The single-object delta functor from short exact module rows to the derived category. -/
@[stacks 0150 "single-complex derived delta functor"]
abbrev single (X : RingedSpace.{u}) :
    DeltaFunctor X.Modules (DerivedCategory X.Modules) where
  toFunctor := DerivedCategory.singleFunctor X.Modules 0
  additive := inferInstance
  δ := fun {_} hS ↦ hS.singleδ
  map_distinguished := fun {_} hS ↦ hS.singleTriangle_distinguished
  δ_naturality := sorry

/-- The derived-global-sections delta functor before taking homology. -/
@[stacks 0151 "derived global-sections delta functor"]
abbrev derived (X : RingedSpace.{u}) :
    DeltaFunctor X.Modules
      (DerivedCategory (ModuleCat (globalSectionsRing X))) :=
  (single X).postcomposeExactFunctor (Module.Derived.GlobalSections.functor X)

/-- The degree `-1` vanishing input for the global cohomology delta functor. -/
@[stacks 05SR "negative-degree global cohomology vanishing"]
theorem hneg (X : RingedSpace.{u}) (ℳ : X.Modules) :
    IsZero
      (((DerivedCategory.homologyFunctor (ModuleCat (globalSectionsRing X)) 0).shift (-1)).obj
        ((derived X).obj ℳ)) := sorry

/-- The canonical cohomological delta functor computing module cohomology on `X`. -/
@[stacks 05SR "global cohomological delta functor"]
abbrev cohomology (X : RingedSpace.{u}) :
    CohomologicalDeltaFunctor X.Modules (ModuleCat (globalSectionsRing X)) :=
  (derived X).toCohomologicalDeltaFunctor
    (DerivedCategory.homologyFunctor (ModuleCat (globalSectionsRing X)) 0)
    (hneg X)

/-- Each degree of global cohomology is linear over the global-sections ring. -/
@[stacks 0EHA "linearity of global cohomology"]
noncomputable instance linear (X : RingedSpace.{u}) (p : ℕ) :
    Functor.Linear (globalSectionsRing X) (((cohomology X).F p).obj) := sorry

/-- The degreewise global cohomology functor agrees with the top-open module cohomology owner. -/
@[stacks 0EHA "global cohomology degree owner"]
theorem degree_obj_eq_moduleCohomologyAtOpen
    (X : RingedSpace.{u}) (ℱ : X.Modules) (p : ℕ) :
    (((cohomology X).F p).obj).obj ℱ =
      moduleCohomologyAtOpen (⊤ : Opens X.carrier) ℱ p := sorry

/-- A global-section scalar map is sent to the corresponding scalar map on cohomology. -/
@[stacks 0EHA "global cohomology scalar map"]
theorem map_smul (X : RingedSpace.{u}) (f : globalSectionsRing X)
    (ℱ : X.Modules) (p n : ℕ) :
    ((cohomology X).F p).obj.map ((f ^ n) • 𝟙 ℱ) =
      (f ^ n) • 𝟙 (((cohomology X).F p).obj.obj ℱ) := sorry

end AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Delta
