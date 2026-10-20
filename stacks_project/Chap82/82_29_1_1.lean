module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ChernTensor

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open scoped BigOperators MonoidalCategory

universe u

/- 82.29.1.1: In Situation 82.2.1, for good `X / B`, a finite locally free
`𝒪_X`-module `E` of rank `r`, and an invertible `𝒪_X`-module `L`, the identity
`c_i(E ⊗ L) = ∑ j, Nat.choose (r + j - i) j • c_{i-j}(E) * c_1(L)^j`
holds in Chow cohomology `A^*(X)` of `X` relative to `f` and `δ`. -/
@[stacks 0ES5] #check (AlgebraicGeometry.AlgebraicSpace.chernClass_tensor_invertible :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E L : X.Modules) (r i : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E] [isInvertibleObject L]
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (k : ℤ) (α : chowGroup (g ≫ f) δ k),
    (ChernClass.chernClass δ f (E ⊗ L) i).cap g k α =
      ∑ j ∈ Finset.range (i + 1),
        Nat.choose (r + j - i) j •
          (if hj : j ≤ i then
            ChowCohomology.castChowGroup δ (g ≫ f)
              (show (k - (j : ℤ)) - ((i - j : ℕ) : ℤ) = k - (i : ℤ) by
                rw [Nat.cast_sub hj]
                omega)
              ((ChernClass.chernClass δ f E (i - j)).cap g (k - (j : ℤ))
                (ChowCohomology.powCap (ChernClass.chernClass δ f L 1).cap j g k α))
          else 0))
