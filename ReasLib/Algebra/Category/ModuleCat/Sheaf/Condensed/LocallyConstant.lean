/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

/-
  Concrete finite CompHaus consumers of the condensed-module adapter.
-/

import Mathlib.Condensed.Discrete.Module
import ReasLib.Algebra.Category.ModuleCat.Sheaf.Condensed

open CategoryTheory
open CategoryTheory.Functor
open Opposite
open LocallyConstant
open CompHausLike

noncomputable section

universe u

namespace ReasLib.Condensed

variable (R : Type (u + 1)) [CommRing R]

/-- A two-point finite compact Hausdorff space, lifted to the site universe. -/
abbrev X₂ : Site.{u} := CompHaus.of (ULift.{u} (Fin 2))
abbrev X₁ : Site.{u} := CompHaus.of (ULift.{u} (Fin 1))

/-- Inclusion of the first point of the one-point space into the two-point space. -/
def inclusion : X₁.{u} ⟶ X₂.{u} :=
  CompHausLike.ofHom _
    { toFun := fun x => ULift.up (Fin.castSucc x.down)
      continuous_toFun := by fun_prop }

/-- The constant projection from the two-point space to the one-point space. -/
def projection : X₂.{u} ⟶ X₁.{u} :=
  CompHausLike.ofHom _
    { toFun := fun _ => ULift.up (0 : Fin 1)
      continuous_toFun := continuous_const }

/-- The native locally constant condensed module used by the consumer. -/
abbrev locallyConstant (P : ModuleCat.{u + 1} R) : CondensedMod.{u} R :=
  (CondensedMod.LocallyConstant.functor R).obj P

/-- The adapter output for the native locally constant module. -/
abbrev locallyConstantSheaf (P : ModuleCat.{u + 1} R) :
    SheafOfModules.{u + 1} (constantRingSheaf R) :=
  moduleSheaf R (locallyConstant R P)

/-- Existing ringed-site section restriction evaluates to the underlying presheaf map. -/
theorem sectionRestriction_inclusion (P : ModuleCat.{u + 1} R)
    (s : (SheafOfModules.evaluation (constantRingSheaf R) (op X₂.{u})).obj
      (locallyConstantSheaf R P)) :
    SheafOfModules.RingedSite.sectionRestriction topology.{u} (constantCommRingSheaf R)
        inclusion.{u} (locallyConstantSheaf R P) s =
      (locallyConstantSheaf R P).val.map inclusion.{u}.op s := by
  rfl

theorem sectionRestriction_projection (P : ModuleCat.{u + 1} R)
    (t : (SheafOfModules.evaluation (constantRingSheaf R) (op X₁.{u})).obj
      (locallyConstantSheaf R P)) :
    SheafOfModules.RingedSite.sectionRestriction topology.{u} (constantCommRingSheaf R)
        projection.{u} (locallyConstantSheaf R P) t =
      (locallyConstantSheaf R P).val.map projection.{u}.op t := by
  rfl

/-- The inclusion acts on locally constant sections by the native linear pullback. -/
theorem locallyConstant_inclusion (P : ModuleCat.{u + 1} R)
    (s : LocallyConstant X₂.{u} P) :
    ((locallyConstant R P).obj.map inclusion.{u}.op).hom s =
      LocallyConstant.comapₗ R inclusion.{u}.hom.hom s := by
  rfl

/-- The projection acts on locally constant sections by the native linear pullback. -/
theorem locallyConstant_projection (P : ModuleCat.{u + 1} R)
    (t : LocallyConstant X₁.{u} P) :
    ((locallyConstant R P).obj.map projection.{u}.op).hom t =
      LocallyConstant.comapₗ R projection.{u}.hom.hom t := by
  rfl

/-- Comparison transports the inclusion action to the output module sheaf. -/
theorem comparison_inclusion (P : ModuleCat.{u + 1} R)
    (s : (modulePresheaf R (locallyConstant R P)).obj (op X₂.{u})) :
    ((comparison R (locallyConstant R P)).app (op X₁.{u})).hom
        ((modulePresheaf R (locallyConstant R P)).map inclusion.{u}.op s) =
      (locallyConstantSheaf R P).val.map inclusion.{u}.op
        (((comparison R (locallyConstant R P)).app (op X₂.{u})).hom s) := by
  exact PresheafOfModules.naturality_apply (comparison R (locallyConstant R P))
    inclusion.{u}.op s

/-- Comparison transports the projection action to the output module sheaf. -/
theorem comparison_projection (P : ModuleCat.{u + 1} R)
    (t : (modulePresheaf R (locallyConstant R P)).obj (op X₁.{u})) :
    ((comparison R (locallyConstant R P)).app (op X₂.{u})).hom
        ((modulePresheaf R (locallyConstant R P)).map projection.{u}.op t) =
      (locallyConstantSheaf R P).val.map projection.{u}.op
        (((comparison R (locallyConstant R P)).app (op X₁.{u})).hom t) := by
  exact PresheafOfModules.naturality_apply (comparison R (locallyConstant R P))
    projection.{u}.op t

/-- On the one-point space, inclusion restricts to the first value. -/
theorem locallyConstant_inclusion_apply (P : ModuleCat.{u + 1} R)
    (s : LocallyConstant X₂.{u} P) (x : ULift.{u} (Fin 1)) :
    LocallyConstant.toFun (X := X₁.{u}) (Y := P)
      (((locallyConstant R P).obj.map inclusion.{u}.op).hom s) x =
      s (ULift.up (Fin.castSucc x.down)) := rfl

/-- Projection pulls a section back to its constant value. -/
theorem locallyConstant_projection_apply (P : ModuleCat.{u + 1} R)
    (t : LocallyConstant X₁.{u} P) (x : ULift.{u} (Fin 2)) :
    LocallyConstant.toFun (X := X₂.{u}) (Y := P)
      (((locallyConstant R P).obj.map projection.{u}.op).hom t) x =
      t (ULift.up (0 : Fin 1)) := rfl

end ReasLib.Condensed
