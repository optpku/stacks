/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CardinalGeneration
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The quasi-coherent subobjects of `ℱ` that are `κ`-generated. -/
def kappaGeneratedQuasiCoherentSubobjects
    (κ : Cardinal.{u}) (ℱ : X.Modules) : Set (Subobject ℱ) :=
  { G | ((G : X.Modules)).IsQuasicoherent ∧ ((G : X.Modules)).IsKappaGenerated κ }

/-- A subobject belongs to `kappaGeneratedQuasiCoherentSubobjects κ ℱ` exactly when its
underlying module is quasi-coherent and `κ`-generated. -/
@[simp] theorem mem_kappaGeneratedQuasiCoherentSubobjects
    (κ : Cardinal.{u}) (ℱ : X.Modules) (G : Subobject ℱ) :
    G ∈ kappaGeneratedQuasiCoherentSubobjects κ ℱ ↔
      ((G : X.Modules)).IsQuasicoherent ∧ ((G : X.Modules)).IsKappaGenerated κ :=
  Iff.rfl

/-- Every scheme admits a cardinal that uniformly bounds a directed, exhaustive family of
quasi-coherent generated subobjects of each quasi-coherent module. -/
theorem exists_cardinal_kappaGeneratedQuasiCoherentSubobjects_isDirectedColimit
    (X : Scheme.{u}) :
    ∃ κ : Cardinal.{u},
      ∀ (ℱ : X.Modules), ℱ.IsQuasicoherent →
        DirectedOn (· ≤ ·) (kappaGeneratedQuasiCoherentSubobjects κ ℱ) ∧
          IsLUB (kappaGeneratedQuasiCoherentSubobjects κ ℱ) (⊤ : Subobject ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules

end
