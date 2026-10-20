module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle.CohenMacaulay

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle

/- Lemma 42.54.6: in Situation 42.7.1, if `𝒩` is a rank-`r` virtual normal sheaf
for a closed subscheme `Z` of `X`, `Y ⟶ X` is locally of finite type, every
irreducible component of `Y` has `δ`-dimension `n`, `dim_δ(Z ×_X Y) ≤ n - r`,
and `O_{Y, ξ}` is Cohen–Macaulay at every point `ξ` of the fibre product with
`δ(ξ) = n - r`, then `c(Z ⟶ X, 𝒩) ∩ [Y]ₙ = [Z ×_X Y]_{n - r}` in
`CH_{n-r}(Z ×_X Y)`. -/
@[stacks 0FEA]
#check (AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.cap_fundamental_eq_fiberFundamental :
  ∀ {S X Y Z W : Scheme.{u}} [UniversallyCatenary S]
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
      CohenMacaulayRing (Y.presheaf.stalk (i' ξ))),
    (globalClassOfRank δ pZ pX i hi V D r).cap
      (Over.homMk j hj : Over.mk pW ⟶ Over.mk pZ)
      (Over.homMk i' hi' : Over.mk pW ⟶ Over.mk pY)
      (Over.homMk f hf : Over.mk pY ⟶ Over.mk pX)
      square n
      (RelativeChow.fundamentalClass δ (Over.mk pY) n) =
      RelativeChow.fundamentalClass δ (Over.mk pW) (n - (r : ℤ)))

end AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
