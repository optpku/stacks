/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Exterior powers of module sheaves on ringed spaces

The degree-`n` exterior power of a module sheaf is obtained by taking sectionwise exterior powers
of its underlying module presheaf and then sheafifying. The construction is exposed as a functor,
so maps and their functoriality are inherited from the generic presheaf owner. Multiplication and
the graded algebra live in focused downstream modules.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ExteriorPower

/-- The objectwise exterior power of sections over an open of `X`. -/
@[stacks 01CG "objectwise exterior power on a ringed space"]
abbrev obj {X : RingedSpace.{u}} (F : X.Modules) (n : ℕ)
    (U : (TopologicalSpace.Opens X)ᵒᵖ) : ModuleCat (X.presheaf.obj U) :=
  PresheafOfModules.ExteriorPower.obj X.presheaf F.val n U

/-- The sectionwise degree-`n` exterior-power presheaf underlying a module sheaf on `X`. -/
@[stacks 01CG "sectionwise exterior power on a ringed space"]
noncomputable abbrev presheaf {X : RingedSpace.{u}} (F : X.Modules) (n : ℕ) :
    X.PresheafModules :=
  SheafOfModules.RingedSite.ExteriorPower.presheaf X.sheaf F n

/-- Evaluation of the sectionwise exterior-power presheaf at an open of `X`. -/
@[simp, stacks 01CG "objectwise exterior power on a ringed space"]
theorem presheaf_obj {X : RingedSpace.{u}} (F : X.Modules) (n : ℕ)
    (U : (TopologicalSpace.Opens X)ᵒᵖ) :
    (presheaf F n).obj U = obj F n U := sorry

/-- The morphism of sectionwise exterior-power presheaves induced by a morphism of module
sheaves. -/
@[stacks 01CG "map on sectionwise exterior powers on a ringed space"]
noncomputable abbrev presheafMap {X : RingedSpace.{u}} {F G : X.Modules}
    (f : F ⟶ G) (n : ℕ) : presheaf F n ⟶ presheaf G n :=
  SheafOfModules.RingedSite.ExteriorPower.presheafMap X.sheaf f n

/-- The degree-`n` exterior-power functor on module sheaves over a ringed space. -/
@[stacks 01CG "exterior-power functor on a ringed space"]
noncomputable def functor (X : RingedSpace.{u}) (n : ℕ) :
    CategoryTheory.Functor X.Modules X.Modules :=
  SheafOfModules.RingedSite.ExteriorPower.functor X.sheaf n

/-- The degree-`n` exterior-power sheaf of `F`. -/
@[stacks 01CG "exterior power of a module sheaf"]
noncomputable abbrev sheaf {X : RingedSpace.{u}} (F : X.Modules) (n : ℕ) : X.Modules :=
  SheafOfModules.RingedSite.ExteriorPower.sheaf X.sheaf F n

/-- The sheaf `Λ[n] F` is the sheafification of the sectionwise degree-`n` exterior-power
presheaf. -/
@[stacks 01CG "exterior power as a sheafification"]
theorem sheaf_eq_sheafification {X : RingedSpace.{u}}
    (F : X.Modules) (n : ℕ) :
    sheaf F n = (moduleSheafification X).obj (presheaf F n) := sorry

/-- The canonical isomorphism from the sheafification model to the exterior-power sheaf. -/
@[stacks 01CG "canonical ringed-space exterior-power sheafification isomorphism"]
noncomputable abbrev sheafificationIso {X : RingedSpace.{u}}
    (F : X.Modules) (n : ℕ) :
    (moduleSheafification X).obj (presheaf F n) ≅ sheaf F n :=
  SheafOfModules.RingedSite.ExteriorPower.sheafificationIso (𝒪 := X.sheaf) F n

/-- The morphism on degree-`n` exterior-power sheaves induced by a morphism of module sheaves. -/
@[stacks 01CG "map on exterior powers on a ringed space"]
noncomputable abbrev map {X : RingedSpace.{u}} {F G : X.Modules}
    (f : F ⟶ G) (n : ℕ) : sheaf F n ⟶ sheaf G n :=
  SheafOfModules.RingedSite.ExteriorPower.map X.sheaf f n

/-- The isomorphism on exterior-power sheaves induced by a module-sheaf isomorphism. -/
@[stacks 01CG "ringed-space exterior power of a module-sheaf isomorphism"]
noncomputable abbrev mapIso {X : RingedSpace.{u}} {F G : X.Modules}
    (e : F ≅ G) (n : ℕ) : sheaf F n ≅ sheaf G n :=
  SheafOfModules.RingedSite.ExteriorPower.mapIso (𝒪 := X.sheaf) e n

/-- On underlying presheaves, the exterior-power sheaf map is the sheafification of the
sectionwise exterior-power map. -/
@[stacks 01CG "exterior-power map as a sheafification on a ringed space"]
theorem map_eq_sheafification {X : RingedSpace.{u}} {F G : X.Modules}
    (f : F ⟶ G) (n : ℕ) :
    map f n = (moduleSheafification X).map (presheafMap f n) := sorry

end AlgebraicGeometry.RingedSpace.ExteriorPower

/- The scoped notation keeps the exterior degree visible without introducing a caret-based
custom superscript syntax. -/
scoped[AlgebraicGeometry] notation3:max "Λ[" n "] " F =>
  AlgebraicGeometry.RingedSpace.ExteriorPower.sheaf F n
