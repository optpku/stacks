/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ChernTensor

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open scoped BigOperators MonoidalCategory

universe u

/- Lemma 82.29.1: In Situation 82.2.1 let `X / B` be good. Let `E` be a
finite locally free `𝒪_X`-module of rank `r`, and let `L` be an invertible
`𝒪_X`-module. Then
`c_i(E ⊗ L) = ∑_{j=0}^i Nat.choose (r + j - i) j • c_{i-j}(E) * c₁(L)^j`
in `A^*(X)`. -/
@[stacks 0ES4] #check (AlgebraicGeometry.AlgebraicSpace.chernClass_tensor_invertible :
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
