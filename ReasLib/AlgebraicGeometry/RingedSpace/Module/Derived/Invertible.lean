/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Invertible
public import ReasLib.AlgebraicGeometry.RingedSpace.LocallyRinged
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Locally shifted invertible derived modules on ringed spaces

This file specializes the bundled ringed-site owner to the canonical opens ringed site.  It also
exposes the local shifted-module characterization of invertibility using either ambient stalk
instances or an explicit stalkwise local-ring hypothesis.
-/

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open RingedSite (ModuleCat)
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

namespace ModuleDerived

/-- Locally shifted invertible objects of `D(𝒪_X)` for the canonical ordinary module-sheaf
tensor on the localized opens sites, as an object property. -/
@[stacks 0FPG "local shifted-invertibility on a ringed space"]
abbrev locallyShiftedInvertible : ObjectProperty (ModuleDerived X) :=
  letI : ∀ U : Opens X,
      MonoidalCategory (ModuleCat ((opensRingedSite X).localization U)) :=
    fun U ↦ SheafOfModules.RingedSite.ModuleOver.monoidalCategory X.sheaf U
  RingedSite.Hom.ModuleDerived.locallyShiftedInvertible (X := opensRingedSite X)

/-- An object of `D(𝒪_X)` is locally shifted invertible when it belongs to
`locallyShiftedInvertible`. -/
@[stacks 0FPG "local shifted-invertibility predicate on a ringed space"]
abbrev IsLocallyShiftedInvertible (M : ModuleDerived X) : Prop :=
  locallyShiftedInvertible (X := X) M

/-- Locally shifted invertible objects of `D(𝒪_X)`, as a full subcategory. -/
@[stacks 0FPG "local shifted-invertibility full subcategory on a ringed space"]
abbrev LocallyShiftedInvertible :=
  (locallyShiftedInvertible (X := X)).FullSubcategory

namespace LocallyShiftedInvertible

/-- The canonical inclusion of locally shifted invertible objects of `D(𝒪_X)`. -/
@[stacks 0FPG "local shifted-invertibility inclusion on a ringed space"]
abbrev ι : LocallyShiftedInvertible (X := X) ⥤ ModuleDerived X :=
  ObjectProperty.ι _

end LocallyShiftedInvertible

end ModuleDerived

/-- Lemma 20.52.2 with local stalk-ring instances: invertibility for the canonical K-flat
derived tensor is equivalent to local shifted invertibility for the ordinary module tensor. -/
@[stacks 0FPG "local criterion for canonical derived invertibility"]
theorem isInvertible_iff_isLocallyShiftedInvertible
    [ModuleDerived.KFlat.HomotopyTensorDescends X] [ModuleDerived.KFlat.TensorDescends X]
    [ModuleDerived.KFlat.IsLocalization X]
    [∀ x : X, IsLocalRing (X.presheaf.stalk x)] (M : ModuleDerived X) :
    letI := ModuleDerived.monoidalCategory X
    Functor.IsEquivalence (tensorRight M) ↔ M.IsLocallyShiftedInvertible := sorry

/-- Lemma 20.52.2: if all stalk rings of `X` are local, an object of `D(𝒪_X)` is
invertible exactly when it is locally a shift of an invertible module. -/
@[stacks 0FPG]
theorem isInvertible_iff_isLocallyShiftedInvertible_of_stalk_isLocalRing
    [ModuleDerived.KFlat.HomotopyTensorDescends X] [ModuleDerived.KFlat.TensorDescends X]
    [ModuleDerived.KFlat.IsLocalization X]
    (M : ModuleDerived X)
    (h_local : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    letI := ModuleDerived.monoidalCategory X
    Functor.IsEquivalence (tensorRight M) ↔ M.IsLocallyShiftedInvertible := sorry

end AlgebraicGeometry.RingedSpace
