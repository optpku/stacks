/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Dense
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Valuative reductions for extension-dense classes of discrete valuation rings
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ValuativeCriterion.DVR.Uniqueness

/-- If `P` is
an extension-dense class of discrete valuation rings and every valuative square
whose ring lies in `P` has at most one lift, then `f` satisfies DVR uniqueness. -/
theorem of_extensionDense
    {P : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R], Prop}
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsDiscreteValuationRing.ExtensionDense P]
    (h : ∀ (sq : ValuativeCommSq f) [IsDiscreteValuationRing sq.R],
      P sq.R → Subsingleton sq.commSq.LiftStruct) :
    Uniqueness f :=
  sorry

end ValuativeCriterion.DVR.Uniqueness

namespace ValuativeCriterion.DVR.Existence

/-- If `f` is
separated and `P` is an extension-dense class of discrete valuation rings such
that every valuative square whose ring lies in `P` admits a `P`-valued
extension with a lift, then `f` satisfies DVR existence. -/
theorem of_extensionDense
    {P : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R], Prop}
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] [IsDiscreteValuationRing.ExtensionDense P]
    (h : ∀ (sq : ValuativeCommSq f) [IsDiscreteValuationRing sq.R],
      P sq.R → ∃ (e : sq.Extension) (hR' : IsDiscreteValuationRing e.R'), P e.R') :
    Existence f :=
  sorry

end ValuativeCriterion.DVR.Existence

end AlgebraicGeometry.AlgebraicSpace
