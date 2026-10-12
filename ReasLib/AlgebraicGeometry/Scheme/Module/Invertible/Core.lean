/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Core
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- The core groupoid of invertible modules on a scheme. -/
abbrev Core (X : Scheme.{u}) : Type (u + 1) :=
  CategoryTheory.Core
    (ObjectProperty.FullSubcategory (fun L : X.Modules ↦ Scheme.Modules.Invertible L))

/-- The underlying scheme module of an object in the core of invertible modules. -/
def inclusion (X : Scheme.{u}) : Core X ⥤ X.Modules :=
  CategoryTheory.Core.inclusion _ ⋙ ObjectProperty.ι _

/-- Objects of the invertible-module core are invertible after forgetting to scheme modules. -/
theorem core_obj_invertible (X : Scheme.{u}) (L : Core X) :
    Scheme.Modules.Invertible ((inclusion X).obj L) := sorry

/-- Evaluation on an open gives the module of sections of an invertible module. -/
def sections (X : Scheme.{u}) (U : X.Opens) :
    Core X ⥤ ModuleCat Γ(X, U) :=
  inclusion X ⋙ RingedSpace.moduleSectionsEvaluationFunctor X.toRingedSpace U

/-- The sections functor evaluates the underlying invertible module on the chosen open. -/
theorem sections_obj (X : Scheme.{u}) (U : X.Opens) (L : Core X) :
    (sections X U).obj L =
      (RingedSpace.moduleSectionsEvaluationFunctor X.toRingedSpace U).obj
        ((inclusion X).obj L) := sorry

end AlgebraicGeometry.Scheme.Modules.Invertible

end
