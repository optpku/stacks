/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle.ClosedImmersion
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.TopChern
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative.Cycle
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative.Reindex
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle

/-- For a cartesian square whose base-changed immersion is regular of conormal rank `r`,
the virtual-normal class capped with the fundamental class of a scheme of dimension `n`
agrees in every degree with the excess top Chern class capped with the degree-`n - r`
fundamental class of the fiber product. Components below degree `r` vanish. -/
theorem cap_fundamental_eq_topChern
    {S X Y Z W : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (pX : X ⟶ S) (pY : Y ⟶ S) (pZ : Z ⟶ S) (pW : W ⟶ S)
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    [LocallyOfFiniteType pZ] [LocallyOfFiniteType pW]
    (i : Z ⟶ X) (hi : i ≫ pX = pZ) [IsClosedImmersion i]
    (f : Y ⟶ X) (hf : f ≫ pX = pY) [LocallyOfFiniteType f]
    (j : W ⟶ Z) (hj : j ≫ pZ = pW)
    (i' : W ⟶ Y) (hi' : i' ≫ pY = pW) [IsRegularClosedImmersion i']
    (square : IsPullback j i' i f)
    (V : VirtualNormalBundle i)
    (D : ClosedDeformation pZ pX i hi V)
    (V' : VirtualNormalBundle i') [IsIso V'.map]
    (E : W.Modules) [E.IsFiniteLocallyFree]
    (ι : V'.module ⟶ (pullback square V).module)
    (πE : (pullback square V).module ⟶ E)
    (hzero : ι ≫ πE = 0)
    (hshort : (ShortComplex.mk ι πE hzero).ShortExact)
    (hfactor : (pullback square V).map = Scheme.Modules.dualMap ι ≫ V'.map)
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (conormalSheaf i')]
    (n : ℤ)
    (hY : (⨆ η : genericPoints Y,
      (pY.relativeDimensionFunction δ η.1 : EInt)) = (n : EInt)) :
    ∀ q : ℕ,
      (globalClassOfRank δ pZ pX i hi V D q).cap
        (Over.homMk j hj : Over.mk pW ⟶ Over.mk pZ)
        (Over.homMk i' hi' : Over.mk pW ⟶ Over.mk pY)
        (Over.homMk f hf : Over.mk pY ⟶ Over.mk pX)
        square n (RelativeChow.fundamentalClass δ (Over.mk pY) n) =
      if h : r ≤ q then
        RelativeChow.castDegree δ (by rw [Nat.cast_sub h]; omega)
          ((ChernClass.topDegreeOfRankComponents δ pW E
            (fun s ↦ ChernClass.rankComponent δ pW E s ⟨s, Nat.lt_succ_self s⟩)
            (q - r)).cap
              (𝟙 (Over.mk pW)) (𝟙 (Over.mk pW)) (𝟙 (Over.mk pW))
              IsPullback.of_id_snd (n - r)
              (RelativeChow.fundamentalClass δ (Over.mk pW) (n - r)))
      else 0 :=
  sorry

/-- The degree-`r + e` virtual-normal class capped with the fundamental class equals
the degree-`e` excess top Chern class capped with the degree-`n - r` fundamental class,
after identifying their common output degree `n - r - e`. -/
theorem cap_fundamental_eq_topChern_homogeneous
    {S X Y Z W : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (pX : X ⟶ S) (pY : Y ⟶ S) (pZ : Z ⟶ S) (pW : W ⟶ S)
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    [LocallyOfFiniteType pZ] [LocallyOfFiniteType pW]
    (i : Z ⟶ X) (hi : i ≫ pX = pZ) [IsClosedImmersion i]
    (f : Y ⟶ X) (hf : f ≫ pX = pY) [LocallyOfFiniteType f]
    (j : W ⟶ Z) (hj : j ≫ pZ = pW)
    (i' : W ⟶ Y) (hi' : i' ≫ pY = pW) [IsRegularClosedImmersion i']
    (square : IsPullback j i' i f)
    (V : VirtualNormalBundle i)
    (D : ClosedDeformation pZ pX i hi V)
    (V' : VirtualNormalBundle i') [IsIso V'.map]
    (E : W.Modules) [E.IsFiniteLocallyFree]
    (ι : V'.module ⟶ (pullback square V).module)
    (πE : (pullback square V).module ⟶ E)
    (hzero : ι ≫ πE = 0)
    (hshort : (ShortComplex.mk ι πE hzero).ShortExact)
    (hfactor : (pullback square V).map = Scheme.Modules.dualMap ι ≫ V'.map)
    (r e : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (conormalSheaf i')]
    (n : ℤ)
    (hY : (⨆ η : genericPoints Y,
      (pY.relativeDimensionFunction δ η.1 : EInt)) = (n : EInt)) :
    RelativeChow.castDegree δ (by simp only [Nat.cast_add]; omega)
      ((globalClassOfRank δ pZ pX i hi V D (r + e)).cap
        (Over.homMk j hj : Over.mk pW ⟶ Over.mk pZ)
        (Over.homMk i' hi' : Over.mk pW ⟶ Over.mk pY)
        (Over.homMk f hf : Over.mk pY ⟶ Over.mk pX)
        square n (RelativeChow.fundamentalClass δ (Over.mk pY) n)) =
      (ChernClass.topDegreeOfRankComponents δ pW E
        (fun s ↦ ChernClass.rankComponent δ pW E s ⟨s, Nat.lt_succ_self s⟩) e).cap
        (𝟙 (Over.mk pW)) (𝟙 (Over.mk pW)) (𝟙 (Over.mk pW))
        IsPullback.of_id_snd (n - r)
        (RelativeChow.fundamentalClass δ (Over.mk pW) (n - r)) :=
  sorry

end AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
