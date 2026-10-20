module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.CategoryTheory.CommSq

/-!
# Inertia diagrams of profinite fundamental groups

This module packages the five-object profinite diagram with its displayed maps and
commutativity and triviality laws.
-/

@[expose] public section

universe u

open CategoryTheory

namespace EtaleFundamentalGroup

/-- A profinite fundamental-group diagram with a commuting triangle and square and a trivial
diagonal map. -/
structure InertiaDiagram
    (pi1Ush pi1Uh pi1U pi1Xh pi1X : ProfiniteGrp.{u}) where
  /-- The top-left map `π₁(Uˢʰ) ⟶ π₁(Uʰ)`. -/
  ushToUh : pi1Ush ⟶ pi1Uh
  /-- The top-right map `π₁(Uʰ) ⟶ π₁(U)`. -/
  uhToU : pi1Uh ⟶ pi1U
  /-- The left vertical map `π₁(Uʰ) ⟶ π₁(Xʰ)`. -/
  uhToXh : pi1Uh ⟶ pi1Xh
  /-- The right vertical map `π₁(U) ⟶ π₁(X)`. -/
  uToX : pi1U ⟶ pi1X
  /-- The bottom map `π₁(Xʰ) ⟶ π₁(X)`. -/
  xhToX : pi1Xh ⟶ pi1X
  /-- The diagonal map `π₁(Uˢʰ) ⟶ π₁(Xʰ)`. -/
  ushToXh : pi1Ush ⟶ pi1Xh
  /-- The diagonal agrees with the composite through `π₁(Uʰ)`. -/
  triangle : ushToUh ≫ uhToXh = ushToXh
  /-- The square from `π₁(Uʰ)` to `π₁(X)` commutes. -/
  square : CategoryTheory.CommSq uhToU uhToXh uToX xhToX
  /-- The diagonal map is trivial, as indicated by the label `1`. -/
  diagonalTrivial : ∀ g : pi1Ush, ushToXh g = 1

/-- Construct a profinite fundamental-group diagram from its six maps and three laws. -/
def InertiaDiagram.of
    (pi1Ush pi1Uh pi1U pi1Xh pi1X : ProfiniteGrp.{u})
    (ushToUh : pi1Ush ⟶ pi1Uh) (uhToU : pi1Uh ⟶ pi1U)
    (uhToXh : pi1Uh ⟶ pi1Xh) (uToX : pi1U ⟶ pi1X)
    (xhToX : pi1Xh ⟶ pi1X) (ushToXh : pi1Ush ⟶ pi1Xh)
    (triangle : ushToUh ≫ uhToXh = ushToXh)
    (square : CategoryTheory.CommSq uhToU uhToXh uToX xhToX)
    (diagonalTrivial : ∀ g : pi1Ush, ushToXh g = 1) :
    InertiaDiagram pi1Ush pi1Uh pi1U pi1Xh pi1X :=
  { ushToUh := ushToUh
    uhToU := uhToU
    uhToXh := uhToXh
    uToX := uToX
    xhToX := xhToX
    ushToXh := ushToXh
    triangle := triangle
    square := square
    diagonalTrivial := diagonalTrivial }

/-- The defining specification of an inertia diagram exposes its triangle, square, and trivial
diagonal laws together. -/
theorem InertiaDiagram.spec
    {pi1Ush pi1Uh pi1U pi1Xh pi1X : ProfiniteGrp.{u}}
    (D : InertiaDiagram pi1Ush pi1Uh pi1U pi1Xh pi1X) :
    D.ushToUh ≫ D.uhToXh = D.ushToXh ∧
      CategoryTheory.CommSq D.uhToU D.uhToXh D.uToX D.xhToX ∧
        (∀ g : pi1Ush, D.ushToXh g = 1) := sorry

end EtaleFundamentalGroup
