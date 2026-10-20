/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.LocallyFinsupp
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-! # Weight-one pushforward of cycles along closed immersions -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function Set Topology TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Weight-one pushforward along a closed immersion has locally finite support. -/
theorem closedImmersionCyclePushforward_locallyFinite {S : Scheme.{u}}
    {Z X : AlgebraicSpace S} (i : Z ⟶ X) [hClosed : IsClosedImmersion i]
    (α : Function.locallyFinsupp (Points Z) ℤ) :
    LocallyFiniteSupport fun x : Points X ↦
      ∑ᶠ y ∈ Points.map i ⁻¹' {x}, α y :=
  sorry

/-- Weight-one pushforward of a locally finite cycle along a closed immersion. -/
noncomputable def closedImmersionCyclePushforward {S : Scheme.{u}}
    {Z X : AlgebraicSpace S} (i : Z ⟶ X) [hClosed : IsClosedImmersion i]
    (α : Function.locallyFinsupp (Points Z) ℤ) :
    Function.locallyFinsupp (Points X) ℤ where
  toFun := fun x ↦ ∑ᶠ y ∈ Points.map i ⁻¹' {x}, α y
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun x _ ↦
    closedImmersionCyclePushforward_locallyFinite i α x

/-- Pushforward along a closed immersion evaluates by the weight-one sum over
the fibre of its map on points. -/
theorem closedImmersionCyclePushforward_apply {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [hClosed : IsClosedImmersion i] (α : Function.locallyFinsupp (Points Z) ℤ)
    (x : Points X) :
    closedImmersionCyclePushforward i α x = ∑ᶠ y ∈ Points.map i ⁻¹' {x}, α y :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Hom
