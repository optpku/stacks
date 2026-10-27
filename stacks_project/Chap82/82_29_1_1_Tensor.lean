/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module


public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ChernTensor

/-! # Tensor-twist formula for Chern classes on algebraic spaces -/

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open scoped BigOperators MonoidalCategory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.chernClass_tensor_invertible :
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
            (AddEquiv.cast (M := Hom.chowGroup (g ≫ f) δ)
              (show (k - (j : ℤ)) - ((i - j : ℕ) : ℤ) = k - (i : ℤ) by
                rw [Nat.cast_sub hj]
                omega)).toAddMonoidHom
              ((ChernClass.chernClass δ f E (i - j)).cap g (k - (j : ℤ))
                (ChowCohomology.powCap (ChernClass.chernClass δ f L 1).cap j g k α))
          else 0))
