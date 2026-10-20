/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Restriction
public import ReasLib.AlgebraicGeometry.ChowGroup.Supported

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- A bivariant class acts trivially on an ambient Chow class carried by a closed
support disjoint from the image of its source. -/
theorem cap_toAmbient_eq_zero_of_disjoint_support
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Z.hom]
    (f : Z ⟶ X) {p k : ℤ} (c : BivariantClass δ f p)
    (α : ChowGroup.Supported X.hom δ k)
    (hα : Disjoint (α.support : Set X.left) (Set.range f.left.base)) :
    c.cap (𝟙 Z) f (𝟙 X) (IsPullback.id_horiz f.left) k α.toAmbient = 0 := sorry

end AlgebraicGeometry.BivariantClass
