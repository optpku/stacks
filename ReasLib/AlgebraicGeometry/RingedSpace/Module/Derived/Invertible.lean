/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Invertible
public import ReasLib.AlgebraicGeometry.RingedSpace.LocallyRinged
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
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
variable [∀ U : Opens X,
  MonoidalCategory (ModuleCat ((opensRingedSite X).localization U))]

namespace ModuleDerived

/-- Locally shifted invertible objects of `D(𝒪_X)`, as an object property. -/
@[stacks 0FPG "local shifted-invertibility on a ringed space"]
abbrev locallyShiftedInvertible : ObjectProperty (ModuleDerived X) :=
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

variable [MonoidalCategory (ModuleDerived X)]

/-- Ambient-instance form of Lemma 20.52.2: on a ringed space with local stalk rings,
invertibility is equivalent to local shifted invertibility. -/
@[stacks 0FPG "ambient-instance local criterion for derived invertibility"]
theorem isInvertible_iff_isLocallyShiftedInvertible
    [∀ x : X, IsLocalRing (X.presheaf.stalk x)] (M : ModuleDerived X) :
    Functor.IsEquivalence (tensorRight M) ↔ M.IsLocallyShiftedInvertible := sorry

/-- Lemma 20.52.2: if all stalk rings of `X` are local, an object of `D(𝒪_X)` is
invertible exactly when it is locally a shift of an invertible module. -/
@[stacks 0FPG]
theorem isInvertible_iff_isLocallyShiftedInvertible_of_stalk_isLocalRing
    (M : ModuleDerived X)
    (h_local : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    Functor.IsEquivalence (tensorRight M) ↔ M.IsLocallyShiftedInvertible := sorry

end AlgebraicGeometry.RingedSpace
