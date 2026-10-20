/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import stacks_project.Chap42.«42_37_1_1_FundamentalCycle»
public import stacks_project.Chap42.Lemma_42_54_2_BivariantClass
public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle.Fundamental
public import ReasLib.AlgebraicGeometry.ChowGroup.Total

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle

/-- The degree-`n` fundamental class of a scheme locally of finite type over `S`. -/
noncomputable abbrev fundamentalClass_mk
    {S Y : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (pY : Y ⟶ S) [LocallyOfFiniteType pY] (n : ℤ) :
    RelativeChow δ (Over.mk pY) n :=
  RelativeChow.fundamentalClass δ (Over.mk pY) n

/-- An excess-intersection square remains cartesian on the induced morphisms in `Over S`. -/
theorem isPullback_overHom
    {S X Y Z W : Scheme.{u}}
    {pX : X ⟶ S} {pY : Y ⟶ S} {pZ : Z ⟶ S} {pW : W ⟶ S}
    {i : Z ⟶ X} (hi : i ≫ pX = pZ)
    {f : Y ⟶ X} (hf : f ≫ pX = pY)
    {j : W ⟶ Z} (hj : j ≫ pZ = pW)
    {i' : W ⟶ Y} (hi' : i' ≫ pY = pW)
    (square : IsPullback j i' i f) :
    IsPullback
      (Over.homMk j hj : Over.mk pW ⟶ Over.mk pZ).left
      (Over.homMk i' hi' : Over.mk pW ⟶ Over.mk pY).left
      (overHom pZ pX i hi).left
      (Over.homMk f hf : Over.mk pY ⟶ Over.mk pX).left := square

/- Lemma 42.54.5: in an excess-intersection square, if `Y` has `δ`-dimension `n`
and the conormal sheaf of `W := Y ×_X Z` over `Y` has constant rank `r`, then
`c(Z ⟶ X, 𝒩) ∩ [Y]ₙ = c_top(ℰ) ∩ [W]ₙ₋ᵣ` in `CH_*(W)`. -/
@[stacks 0FBM]
#check (AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.cap_fundamental_eq_topChern :
  ∀ {S X Y Z W : Scheme.{u}} [UniversallyCatenary S]
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
      (pY.relativeDimensionFunction δ η.1 : EInt)) = (n : EInt)),
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
      else 0)

#check (AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.cap_fundamental_eq_topChern_homogeneous :
  ∀ {S X Y Z W : Scheme.{u}} [UniversallyCatenary S]
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
      (pY.relativeDimensionFunction δ η.1 : EInt)) = (n : EInt)),
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
        (RelativeChow.fundamentalClass δ (Over.mk pW) (n - r)))

end AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
