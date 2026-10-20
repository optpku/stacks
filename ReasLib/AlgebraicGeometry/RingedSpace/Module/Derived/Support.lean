/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Support of derived modules on ringed spaces

Support for a derived module means that every cohomology sheaf is supported on the specified
subset. This is the ringed-space specialization of `DerivedCategory.cohomologyIn`.
-/

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}

/-- Derived `𝒪_X`-modules whose cohomology sheaves are all supported on `T`. -/
@[stacks 06UQ "derived module support"]
abbrev supportedOn (T : Set X) : ObjectProperty (ModuleDerived X) :=
  DerivedCategory.cohomologyIn (RingedSpace.moduleSupportedOn T)

/-- A derived `𝒪_X`-module is supported on `T` when each of its cohomology sheaves is. -/
abbrev IsSupportedOn (K : ModuleDerived X) (T : Set X) : Prop :=
  supportedOn T K

/-- The full subcategory of derived `𝒪_X`-modules supported on `T`. -/
@[stacks 0AEF "supported derived module subcategory"]
abbrev SupportedOn (T : Set X) :=
  (supportedOn T).FullSubcategory

namespace SupportedOn

/-- The inclusion of derived `𝒪_X`-modules supported on `T` into all derived modules. -/
@[stacks 0AEF "inclusion of supported derived modules"]
abbrev inclusion (T : Set X) : SupportedOn T ⥤ ModuleDerived X :=
  (supportedOn T).ι

end SupportedOn

/-- The derived support condition is the corresponding degreewise cohomology condition. -/
@[simp, stacks 06UQ "derived module support membership"]
theorem isSupportedOn_iff (K : ModuleDerived X) (T : Set X) :
    IsSupportedOn K T ↔
      ∀ i : ℤ, RingedSpace.moduleSupportedOn T
        ((DerivedCategory.homologyFunctor X.Modules i).obj K) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived
