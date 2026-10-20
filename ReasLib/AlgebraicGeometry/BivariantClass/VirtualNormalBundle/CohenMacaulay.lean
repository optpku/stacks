/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle.ClosedImmersion
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative.Cycle
public import ReasLib.RingTheory.CohenMacaulay.Ring

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle

/-- A rank-`r` virtual normal bundle sends the degree-`n` fundamental class of a
scheme of pure dimension `n` to the degree-`n - r` fundamental class of its inverse
image, provided that inverse image has dimension at most `n - r` and the source
stalks at its points of dimension `n - r` are Cohen–Macaulay. -/
theorem cap_fundamental_eq_fiberFundamental
    {S X Y Z W : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (pX : X ⟶ S) (pY : Y ⟶ S) (pZ : Z ⟶ S) (pW : W ⟶ S)
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    [LocallyOfFiniteType pZ] [LocallyOfFiniteType pW]
    (i : Z ⟶ X) (hi : i ≫ pX = pZ) [IsClosedImmersion i]
    (f : Y ⟶ X) (hf : f ≫ pX = pY) [LocallyOfFiniteType f]
    (j : W ⟶ Z) (hj : j ≫ pZ = pW)
    (i' : W ⟶ Y) (hi' : i' ≫ pY = pW)
    (square : IsPullback j i' i f)
    (V : VirtualNormalBundle i)
    (D : ClosedDeformation pZ pX i hi V)
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r V.module] (n : ℤ)
    (hY : ∀ η : genericPoints Y, pY.relativeDimensionFunction δ η.1 = n)
    (hdimW : (⨆ η : genericPoints W,
      (pW.relativeDimensionFunction δ η.1 : EInt)) ≤ (n - (r : ℤ) : EInt))
    (hCM : ∀ ξ : W, pW.relativeDimensionFunction δ ξ = n - (r : ℤ) →
      CohenMacaulayRing (Y.presheaf.stalk (i' ξ))) :
    (globalClassOfRank δ pZ pX i hi V D r).cap
      (Over.homMk j hj : Over.mk pW ⟶ Over.mk pZ)
      (Over.homMk i' hi' : Over.mk pW ⟶ Over.mk pY)
      (Over.homMk f hf : Over.mk pY ⟶ Over.mk pX)
      square n
      (RelativeChow.fundamentalClass δ (Over.mk pY) n) =
      RelativeChow.fundamentalClass δ (Over.mk pW) (n - (r : ℤ)) := sorry

end AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
