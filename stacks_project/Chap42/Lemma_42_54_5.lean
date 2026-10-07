module

public import stacks_project.Chap42.«42_37_1_1_FundamentalCycle»
public import stacks_project.Chap42.Lemma_42_54_2_BivariantClass
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.TopChern
public import ReasLib.AlgebraicGeometry.ChowGroup.Total
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom
namespace VirtualNormalBundle

/-- The degree-`n` fundamental class of a scheme locally of finite type over `S`. -/
noncomputable def fundamentalClass_mk
    {S Y : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (pY : Y ⟶ S) [LocallyOfFiniteType pY] (n : ℤ) :
    RelativeChow δ (Over.mk pY) n :=
  @chowClass Y (LocallyOfFiniteType.isLocallyNoetherian pY)
    (pY.relativeDimensionFunction δ) _ n
    (@CycleGroup.fundamental Y (LocallyOfFiniteType.isLocallyNoetherian pY)
      (pY.relativeDimensionFunction δ) n)

/-- `fundamentalClass_mk` is the Chow class of the fundamental cycle. -/
theorem fundamentalClass_mk_def
    {S Y : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (pY : Y ⟶ S) [LocallyOfFiniteType pY] (n : ℤ) :
    fundamentalClass_mk δ pY n =
      @chowClass Y (LocallyOfFiniteType.isLocallyNoetherian pY)
        (pY.relativeDimensionFunction δ) _ n
        (@CycleGroup.fundamental Y (LocallyOfFiniteType.isLocallyNoetherian pY)
          (pY.relativeDimensionFunction δ) n) := sorry

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
      (Over.homMk f hf : Over.mk pY ⟶ Over.mk pX).left := sorry

/-- Integer grading identity used to compare the two excess-intersection cap degrees. -/
theorem cap_excess_degree (n : ℤ) (r e : ℕ) : n - (r + e) = n - r - e := sorry

/-- Lemma 42.54.5: in an excess-intersection square, if `Y` has `δ`-dimension `n`
and the conormal sheaf of `W := Y ×_X Z` over `Y` has constant rank `r`, then
`c(Z ⟶ X, 𝒩) ∩ [Y]ₙ = c_top(ℰ) ∩ [W]ₙ₋ᵣ` in `CH_*(W)`. -/
@[stacks 0FBM]
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
    (D : ClosedSpecialization δ pZ pX i hi V)
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
    let leftCap :=
      (globalClassOfRank δ pZ pX i hi V D (r + e)).cap
        (Over.homMk j hj : Over.mk pW ⟶ Over.mk pZ)
        (Over.homMk i' hi' : Over.mk pW ⟶ Over.mk pY)
        (Over.homMk f hf : Over.mk pY ⟶ Over.mk pX)
        (isPullback_overHom hi hf hj hi' square) n (fundamentalClass_mk δ pY n)
    let rightCap :=
      (ChernClass.topDegreeOfRankComponents δ pW E
        (fun s ↦ ChernClass.rankComponent δ pW E s ⟨s, Nat.lt_succ_self s⟩) e).cap
        (𝟙 (Over.mk pW)) (𝟙 (Over.mk pW)) (𝟙 (Over.mk pW))
        IsPullback.of_id_snd (n - r) (fundamentalClass_mk δ pW (n - r))
    (DirectSum.of (fun k : ℤ ↦ RelativeChow δ (Over.mk pW) k) (n - r - e)
        (cap_excess_degree n r e ▸ leftCap) :
        ChowGroup.Total δ (Over.mk pW)) =
      DirectSum.of (fun k : ℤ ↦ RelativeChow δ (Over.mk pW) k) (n - r - e) rightCap :=
  sorry

/-- Homogeneous form of the excess-intersection identity in relative Chow homology. -/
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
    (D : ClosedSpecialization δ pZ pX i hi V)
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
    cap_excess_degree n r e ▸
        (globalClassOfRank δ pZ pX i hi V D (r + e)).cap
          (Over.homMk j hj : Over.mk pW ⟶ Over.mk pZ)
          (Over.homMk i' hi' : Over.mk pW ⟶ Over.mk pY)
          (Over.homMk f hf : Over.mk pY ⟶ Over.mk pX)
          (isPullback_overHom hi hf hj hi' square) n (fundamentalClass_mk δ pY n) =
      (ChernClass.topDegreeOfRankComponents δ pW E
        (fun s ↦ ChernClass.rankComponent δ pW E s ⟨s, Nat.lt_succ_self s⟩) e).cap
        (𝟙 (Over.mk pW)) (𝟙 (Over.mk pW)) (𝟙 (Over.mk pW))
        IsPullback.of_id_snd (n - r) (fundamentalClass_mk δ pW (n - r)) :=
  sorry

end VirtualNormalBundle
end Hom
end Scheme
end AlgebraicGeometry

