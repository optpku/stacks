module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Subobject
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Basic

/-!
# Sections of subobjects of module sheaves

This leaf gives the section-level image of a subobject of a module sheaf on an
arbitrary open subset of a ringed space.  Scheme-specific affine-open
specializations belong in `AlgebraicGeometry.Scheme.Module.Sections`.
-/

@[expose] public section

open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Modules

variable {X : RingedSpace.{u}}

/-- The linear map on sections over `U` induced by a subobject of an `𝒪_X`-module. -/
abbrev subobjectSectionsMap
    {ℱ : X.Modules} (𝒢 : Subobject ℱ) (U : Opens X.carrier) :
    ((𝒢 : X.Modules).val.obj (op U)) →ₗ[sectionsRingOnOpen X U] ℱ.val.obj (op U) :=
  (SheafOfModules.Subobject.inclusionApp 𝒢 (op U)).hom

/-- The section submodule over `U` cut out by a subobject of an `𝒪_X`-module. -/
abbrev subobjectSectionsSubmodule
    {ℱ : X.Modules} (𝒢 : Subobject ℱ) (U : Opens X.carrier) :
    Submodule (sectionsRingOnOpen X U) (ℱ.val.obj (op U)) :=
  SheafOfModules.Subobject.sections 𝒢 (op U)

/-- The section submodule of a subobject is the range of its section map. -/
theorem subobjectSectionsSubmodule_def
    {ℱ : X.Modules} (𝒢 : Subobject ℱ) (U : Opens X.carrier) :
    subobjectSectionsSubmodule 𝒢 U = LinearMap.range (subobjectSectionsMap 𝒢 U) := sorry

/-- Membership in the section submodule of a subobject is represented by a section of the
subobject. -/
theorem mem_subobjectSectionsSubmodule
    {ℱ : X.Modules} (𝒢 : Subobject ℱ) (U : Opens X.carrier)
    {x : ℱ.val.obj (op U)} :
    x ∈ subobjectSectionsSubmodule 𝒢 U ↔
      ∃ y : (𝒢 : X.Modules).val.obj (op U), subobjectSectionsMap 𝒢 U y = x := sorry

end AlgebraicGeometry.RingedSpace.Modules
