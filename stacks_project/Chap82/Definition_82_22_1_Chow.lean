/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.ClosedImmersion

/-!
# Chow-level pushforward along closed subspace immersions

The closed-subspace specialization of proper pushforward acts on Chow classes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.chowPushforward :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (W : ClosedSubspace X) (k : ℤ)
      [QuasiSeparated (W.ι ≫ f)] [LocallyOfFiniteType (W.ι ≫ f)],
      Hom.chowGroup (W.ι ≫ f) δ k →+ Hom.chowGroup f δ k)

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.chowPushforward_chowMk :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (W : ClosedSubspace X) (k : ℤ)
      [QuasiSeparated (W.ι ≫ f)] [LocallyOfFiniteType (W.ι ≫ f)]
      (α : Hom.cycleGroup (W.ι ≫ f) δ k),
      Hom.chowPushforward f δ W k (Hom.chowMk (W.ι ≫ f) δ k α) =
        Hom.chowMk f δ k
          (@Hom.properPushforwardHom S B W.X X inferInstance inferInstance
            (W.ι ≫ f) inferInstance inferInstance f inferInstance inferInstance δ inferInstance
            W.ι (@Proper.of_isClosedImmersion S W.X X W.ι W.isClosedImmersion) rfl k α))
