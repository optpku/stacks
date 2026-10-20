/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KFlatResolution
public import ReasLib.Algebra.Homology.DerivedCategory.Monoidal.KFlat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic

@[expose] public section

/-!
# Derived tensor products of modules on ringed spaces

This file assembles the K-flat localization model of the derived category from the canonical
tensor-totalization instances on `Modules X`. Concrete monoidal data require the three explicit
proof boundaries in `ModuleDerived.KFlat`; placeholder proofs of those facts are intentionally not
installed as instances because localization uses them to choose functor and inverse data.
-/

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

namespace KFlat

/-- The condition that totalized tensoring descends from cochain complexes to their homotopy
category. -/
@[stacks 0FPB "homotopy tensor-descends condition"]
abbrev HomotopyTensorDescends (X : RingedSpace.{u}) : Prop :=
  HomotopyCategory.Koszul.TensorDescends (C := Modules X)

/-- The condition that tensoring K-flat homotopy objects preserves restricted
quasi-isomorphisms. -/
@[stacks 0FPB "K-flat tensor-descends condition"]
abbrev TensorDescends (X : RingedSpace.{u}) [HomotopyTensorDescends X] : Prop :=
  HomotopyCategory.KFlat.TensorDescends (C := Modules X)

/-- The condition that K-flat homotopy objects localize to `D(𝒪_X)`. -/
@[stacks 0FPB "K-flat localization condition"]
abbrev IsLocalization (X : RingedSpace.{u}) : Prop :=
  CategoryTheory.DerivedCategory.KFlat.IsLocalization (C := Modules X)

end KFlat

/-- The K-flat resolution theorem for a ringed site, exposed on the canonical `Modules X`
presentation. This named theorem prevents downstream users from rebuilding the opens-site
presentation solely to state the localization property. -/
@[stacks 0FPB "K-flat resolutions on ringed spaces"]
theorem modulesHasKFlatResolutions (X : RingedSpace.{u}) :
    HomotopyCategory.KFlat.HasResolutions (Modules X) := sorry

/-- The derived category of modules on a ringed space carries the tensor product obtained by
localizing K-flat complexes. -/
@[stacks 0FPB "derived tensor product on ringed spaces", instance_reducible]
noncomputable instance monoidalCategory (X : RingedSpace.{u})
    [KFlat.HomotopyTensorDescends X] [KFlat.TensorDescends X]
    [KFlat.IsLocalization X] :
    MonoidalCategory (ModuleDerived X) :=
  CategoryTheory.DerivedCategory.KFlat.monoidalCategory (C := Modules X)

/-- The K-flat derived tensor product of modules on a ringed space is symmetric. -/
@[stacks 0FPB "symmetric derived tensor product on ringed spaces", instance_reducible]
noncomputable instance symmetricCategory (X : RingedSpace.{u})
    [KFlat.HomotopyTensorDescends X] [KFlat.TensorDescends X]
    [KFlat.IsLocalization X] :
    SymmetricCategory (ModuleDerived X) :=
  CategoryTheory.DerivedCategory.KFlat.symmetricCategory (C := Modules X)

section Inference

variable (X : RingedSpace.{u})
variable [KFlat.HomotopyTensorDescends X] [KFlat.TensorDescends X]
variable [KFlat.IsLocalization X]


end Inference

end AlgebraicGeometry.RingedSpace.ModuleDerived
