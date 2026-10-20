/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Invertible.Decomposition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Invertible
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Invertible decompositions of derived modules on ringed spaces

This file specializes locally finite factor decompositions to the canonical opens ringed site of
a ringed space.  The public invertibility statements use the canonical K-flat derived tensor
structure and expose no independently chosen monoidal instance.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}

/-- Locally finite factor ring sheaves on `X`, equipped degreewise with invertible modules. -/
abbrev InvertibleFamily (X : RingedSpace.{u}) :=
  SheafOfModules.RingedSite.InvertibleFamily.{u, u}
    (J := Opens.grothendieckTopology X) X.sheaf

/-- A specified locally finite invertible decomposition of a derived `𝒪_X`-module. -/
abbrev InvertibleDecomposition (M : ModuleDerived X) :=
  SheafOfModules.RingedSite.InvertibleDecomposition.{u, u}
    (J := Opens.grothendieckTopology X) (O := X.sheaf) M

/-- The property that a derived `𝒪_X`-module admits a locally finite invertible
decomposition. -/
abbrev HasInvertibleDecomposition (M : ModuleDerived X) : Prop :=
  SheafOfModules.RingedSite.HasInvertibleDecomposition.{u, u}
    (J := Opens.grothendieckTopology X) (O := X.sheaf) M

variable [KFlat.HomotopyTensorDescends X] [KFlat.TensorDescends X]
variable [KFlat.IsLocalization X]

/-- Lemma 20.52.2 (0FPG), conditions (1) and (2): a derived module is tensor-invertible exactly
when it admits a locally finite decomposition into shifted invertible modules on factor ring
sheaves. -/
@[stacks 0FPG "(1) iff (2)"]
theorem isInvertible_iff_hasDecomposition (M : ModuleDerived X) :
    isInvertibleObject M ↔ HasInvertibleDecomposition M := sorry

/-- Lemma 20.52.2 (0FPG): every tensor-invertible derived module is perfect. -/
@[stacks 0FPG "perfectness"]
theorem isPerfect_of_isInvertible
    {M : ModuleDerived X} (hM : isInvertibleObject M) :
    M.IsPerfect := sorry

/-- Under the local-stalk hypothesis, invertible decomposition is equivalent to being locally a
shift of an invertible module. -/
@[stacks 0FPG "(2) iff (3)"]
theorem hasDecomposition_iff_isLocallyShiftedInvertible_of_stalk_isLocalRing
    (M : ModuleDerived X)
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    HasInvertibleDecomposition M ↔ M.IsLocallyShiftedInvertible := sorry

/-- Lemma 20.52.2 (0FPG): if all structure-sheaf stalks are local rings, tensor invertibility,
locally finite invertible decomposition, and local shifted invertibility are equivalent. -/
@[stacks 0FPG "(1), (2), (3)"]
theorem invertible_tfae_of_stalk_isLocalRing
    (M : ModuleDerived X)
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    ([isInvertibleObject M,
      HasInvertibleDecomposition M,
      M.IsLocallyShiftedInvertible] : List Prop).TFAE := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived
