/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Support
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.ExtensionByZero.Comparison

@[expose] public section

/-!
# Comparing extension by zero with open pushforward under support conditions

The canonical comparison from derived extension by zero to derived open pushforward is invertible
when the cohomology of the input is supported on the inverse image of a closed subset contained in
the open subspace.
-/

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.OpenSubspace.ExtensionByZero

variable {X : RingedSpace.{u}}

/-- The canonical comparison from derived extension by zero to derived open pushforward is an
isomorphism when the input is supported on the inverse image of a closed subset contained in the
open subspace. -/
theorem derivedToPushforward_app_isIso_of_isSupportedOn
    (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})]
    {T : Set X} (hT_closed : IsClosed T) (hTU : T ⊆ U)
    (F : moduleDerivedOnOpen X U)
    (hF : ModuleDerived.IsSupportedOn F (Subtype.val ⁻¹' T)) :
    IsIso ((derivedToPushforward X U).app F) := sorry

/-- Derived extension by zero and derived open pushforward are isomorphic when the input is
supported on the inverse image of a closed subset contained in the open subspace. -/
theorem isIsomorphic_derivedExtensionByZero_pushforward_of_isSupportedOn
    (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})]
    {T : Set X} (hT_closed : IsClosed T) (hTU : T ⊆ U)
    (F : moduleDerivedOnOpen X U)
    (hF : ModuleDerived.IsSupportedOn F (Subtype.val ⁻¹' T)) :
    IsIsomorphic ((moduleExtensionByZeroFromOpenDerived X U).obj F)
      ((modulePushforwardFromOpenDerived U).obj F) := sorry

end AlgebraicGeometry.RingedSpace.OpenSubspace.ExtensionByZero
