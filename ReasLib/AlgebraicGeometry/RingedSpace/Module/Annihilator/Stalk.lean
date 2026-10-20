/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Maps
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Annihilator
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.IdealStalk
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk.InternalHom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalks of annihilator sheaves

The stalk of an annihilator sheaf maps canonically to the structure-sheaf stalk.  This file owns
its image ideal, the unconditional inclusion in the annihilator of the stalk module, and the
finite-type equality.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules.Annihilator

variable {X : RingedSpace.{u}}

open scoped Annihilator

/-- The canonical map from the stalk of `Ann(F)` to the structure-sheaf stalk. -/
@[stacks 0H2I "annihilator stalk map"]
noncomputable abbrev stalkToRing (F : X.Modules) (x : X) :
    RingedSpace.stalkModuleCat (Ann(F)) x ⟶
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x) :=
  RingedSpace.ModuleStalkImage.toRing (ι F) x

/-- The image ideal in `𝒪_{X,x}` of the stalk of `Ann(F)`. -/
@[stacks 0H2I "annihilator stalk ideal"]
noncomputable def stalkIdeal (F : X.Modules) (x : X) :
    Ideal (X.presheaf.stalk x) :=
  RingedSpace.ModuleStalkImage.ideal (ι F) x

/-- Membership in `stalkIdeal F x` is witnessed by an element of the stalk of `Ann(F)`. -/
theorem mem_stalkIdeal_iff (F : X.Modules) (x : X)
    (r : X.presheaf.stalk x) :
    r ∈ stalkIdeal F x ↔
      ∃ s : RingedSpace.stalkModuleCat (Ann(F)) x, (stalkToRing F x).hom s = r := sorry

/-- The annihilator-stalk map sends a germ to the germ of its image in the structure sheaf. -/
theorem stalkToRing_germ (F : X.Modules) (x : X)
    (U : Opens X) (hx : x ∈ U) (s : (Ann(F)).val.obj (op U)) :
    stalkToRing F x (TopCat.Presheaf.germ (Ann(F)).val.presheaf U x hx s) =
      X.presheaf.germ U x hx (sectionToRing F U s) := sorry

/-- The image in `𝒪_{X,x}` of an annihilator-stalk element acts trivially on `F_x`. -/
theorem stalkImage_smul_eq_zero (F : X.Modules) (x : X)
    (s : RingedSpace.stalkModuleCat (Ann(F)) x)
    (m : RingedSpace.stalkModuleCat F x) :
    stalkToRing F x s • m = 0 := sorry

/-- Equation 17.23.1.1: the stalk ideal of `Ann(F)` is contained in the annihilator ideal of
the stalk module `F_x`. -/
@[stacks 0H2I "Equation 17.23.1.1"]
theorem stalkIdeal_le (F : X.Modules) (x : X) :
    stalkIdeal F x ≤
      Module.annihilator (X.presheaf.stalk x) (RingedSpace.stalkModuleCat F x) := sorry

/-- The germ of a local annihilator section belongs to the annihilator ideal of the stalk
module. -/
theorem germ_mem_moduleAnnihilator (F : X.Modules) (x : X)
    (U : Opens X) (hx : x ∈ U) (s : (Ann(F)).val.obj (op U)) :
    X.presheaf.germ U x hx (sectionToRing F U s) ∈
      Module.annihilator (X.presheaf.stalk x) (RingedSpace.stalkModuleCat F x) := sorry

/-- Lemma 17.23.2 (0H2J): for a finite-type module sheaf, the stalk ideal of its annihilator
sheaf equals the annihilator ideal of its stalk module. -/
@[stacks 0H2J]
theorem stalkIdeal_eq (F : X.Modules) (x : X)
    [F.IsFiniteType] :
    stalkIdeal F x =
      Module.annihilator (X.presheaf.stalk x) (RingedSpace.stalkModuleCat F x) := sorry

end SheafOfModules.Annihilator
