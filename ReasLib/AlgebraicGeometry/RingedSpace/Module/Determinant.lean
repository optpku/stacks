/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Determinant
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.Exterior
import Mathlib.Tactic.CrossRefAttribute

/-!
# Determinant sheaves on ringed spaces

This file is the ringed-space facade for the determinant subobject on a commutative ringed site.
All construction data remain owned by the generic ringed-site API.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Determinant

variable {X : RingedSpace.{u}}

/-- The degree-one exterior-algebra action whose kernel defines the determinant sheaf. -/
@[stacks 0FJN "determinant action on a ringed space"]
noncomputable abbrev action (F : X.Modules) :
    ExteriorAlg.sheaf F ⟶
      SheafOfModules.RingedSite.InternalHom.obj X.sheaf F (ExteriorAlg.sheaf F) :=
  SheafOfModules.RingedSite.Determinant.action (𝒪 := X.sheaf) F

/-- The determinant as a subobject of the exterior-algebra sheaf. -/
@[stacks 0FJN "determinant subobject on a ringed space"]
noncomputable abbrev subobject (F : X.Modules) :
    Subobject (ExteriorAlg.sheaf F) :=
  SheafOfModules.RingedSite.Determinant.subobject (𝒪 := X.sheaf) F

/-- The module sheaf underlying the determinant subobject. -/
@[stacks 0FJN "determinant sheaf on a ringed space"]
noncomputable abbrev sheaf (F : X.Modules) : X.Modules :=
  SheafOfModules.RingedSite.Determinant.sheaf (𝒪 := X.sheaf) F

/-- The canonical inclusion of the determinant sheaf into the exterior-algebra sheaf. -/
@[stacks 0FJN "determinant inclusion on a ringed space"]
noncomputable abbrev ι (F : X.Modules) :
    sheaf F ⟶ ExteriorAlg.sheaf F :=
  SheafOfModules.RingedSite.Determinant.ι (𝒪 := X.sheaf) F

/-- The determinant inclusion is annihilated by the degree-one action. -/
@[reassoc, stacks 0FJN "determinant kernel equation on a ringed space"]
theorem ι_comp_action (F : X.Modules) :
    ι F ≫ action F = 0 := sorry

/-- A morphism into the exterior-algebra sheaf factors through the determinant exactly when it
is annihilated by the degree-one action. -/
@[stacks 0FJN "universal property of the determinant on a ringed space"]
theorem factors_iff (F : X.Modules) {K : X.Modules}
    (f : K ⟶ ExteriorAlg.sheaf F) :
    (subobject F).Factors f ↔ f ≫ action F = 0 := sorry

/-- The canonical lift of a morphism annihilated by the degree-one action to the determinant
sheaf. -/
@[stacks 0FJN "lift to the determinant on a ringed space"]
noncomputable abbrev lift (F : X.Modules) {K : X.Modules}
    (f : K ⟶ ExteriorAlg.sheaf F) (h : f ≫ action F = 0) :
    K ⟶ sheaf F :=
  SheafOfModules.RingedSite.Determinant.lift (𝒪 := X.sheaf) F f h

/-- The canonical lift to the determinant recovers the original morphism after the determinant
inclusion. -/
@[reassoc, stacks 0FJN "determinant lift equation on a ringed space"]
theorem lift_ι (F : X.Modules) {K : X.Modules}
    (f : K ⟶ ExteriorAlg.sheaf F) (h : f ≫ action F = 0) :
    lift F f h ≫ ι F = f := sorry

/-- Morphisms into the determinant are determined by their composites with its canonical
inclusion. -/
@[ext, stacks 0FJN "determinant morphism extensionality on a ringed space"]
theorem hom_ext (F : X.Modules) {K : X.Modules}
    {f g : K ⟶ sheaf F} (h : f ≫ ι F = g ≫ ι F) :
    f = g := sorry

set_option maxHeartbeats 800000 in
/-- The forward morphism on determinant sheaves induced by a module-sheaf isomorphism. -/
@[stacks 0FJN "forward morphism on ringed-space determinant sheaves"]
noncomputable abbrev mapIsoHom {F G : X.Modules} (e : F ≅ G) :
    sheaf F ⟶ sheaf G :=
  SheafOfModules.RingedSite.Determinant.mapIsoHom (𝒪 := X.sheaf) e

set_option maxHeartbeats 800000 in
/-- The inverse morphism on determinant sheaves induced by a module-sheaf isomorphism. -/
@[stacks 0FJN "inverse morphism on ringed-space determinant sheaves"]
noncomputable abbrev mapIsoInv {F G : X.Modules} (e : F ≅ G) :
    sheaf G ⟶ sheaf F :=
  SheafOfModules.RingedSite.Determinant.mapIsoInv (𝒪 := X.sheaf) e

set_option maxHeartbeats 800000 in
/-- A module-sheaf isomorphism induces a canonical isomorphism of determinant sheaves. -/
@[stacks 0FJN "ringed-space determinant isomorphism"]
noncomputable abbrev mapIso {F G : X.Modules} (e : F ≅ G) :
    sheaf F ≅ sheaf G :=
  SheafOfModules.RingedSite.Determinant.mapIso (𝒪 := X.sheaf) e

/-- The forward determinant morphism commutes with the canonical exterior-algebra inclusions. -/
@[reassoc, stacks 0FJN "ringed-space determinant morphism inclusion equation"]
theorem mapIsoHom_ι {F G : X.Modules} (e : F ≅ G) :
    mapIsoHom e ≫ ι G = ι F ≫ ExteriorAlg.map e.hom := sorry

/-- The inverse determinant morphism commutes with the canonical exterior-algebra inclusions. -/
@[reassoc, stacks 0FJN "inverse ringed-space determinant morphism inclusion equation"]
theorem mapIsoInv_ι {F G : X.Modules} (e : F ≅ G) :
    mapIsoInv e ≫ ι F = ι G ≫ ExteriorAlg.map e.inv := sorry

/-- The determinant isomorphism commutes with the canonical exterior-algebra inclusions. -/
@[reassoc, stacks 0FJN "ringed-space determinant isomorphism inclusion equation"]
theorem mapIso_hom_ι {F G : X.Modules} (e : F ≅ G) :
    (mapIso e).hom ≫ ι G = ι F ≫ ExteriorAlg.map e.hom := sorry

/-- The identity module-sheaf isomorphism induces the identity determinant isomorphism. -/
@[simp]
theorem mapIso_refl (F : X.Modules) :
    mapIso (Iso.refl F) = Iso.refl (sheaf F) := sorry

/-- Ringed-space determinant isomorphisms respect composition. -/
@[simp]
theorem mapIso_trans {F G H : X.Modules} (e : F ≅ G) (e' : G ≅ H) :
    mapIso (e.trans e') = (mapIso e).trans (mapIso e') := sorry

end AlgebraicGeometry.RingedSpace.Determinant

/-- Scoped notation for the determinant of a module sheaf on a ringed space. -/
scoped[AlgebraicGeometry] notation3:max "det(" F ")" =>
  AlgebraicGeometry.RingedSpace.Determinant.sheaf F

-- The facade selects the canonical monoidal-localization instance.  Its provisional `sorryAx`
-- is confined to that instance's Prop-valued tensor-stability proof; the generic ringed-site
-- determinant data remain explicitly parameterized by the corresponding `IsMonoidal` witness.
