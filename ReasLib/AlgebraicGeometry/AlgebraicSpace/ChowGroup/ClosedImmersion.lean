/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.ProperPushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace

/-! # Chow pushforward from an explicit closed subspace -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
  (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
  (δ : Points B → ℤ) [IsDimensionFunction δ]
  (W : ClosedSubspace X) (k : ℤ)
  [QuasiSeparated (W.ι ≫ f)] [LocallyOfFiniteType (W.ι ≫ f)]

/-- Pushforward on Chow groups along the immersion of an explicit closed subspace. -/
def chowPushforward : chowGroup (W.ι ≫ f) δ k →+ chowGroup f δ k :=
  @ChowGroup.properPushforward S B W.X X inferInstance inferInstance
    (W.ι ≫ f) inferInstance inferInstance f inferInstance inferInstance δ inferInstance
    W.ι (@Proper.of_isClosedImmersion S W.X X W.ι W.isClosedImmersion) rfl k

/-- Closed-subspace Chow pushforward is computed by proper cycle pushforward. -/
theorem chowPushforward_chowMk (α : cycleGroup (W.ι ≫ f) δ k) :
    chowPushforward f δ W k (chowMk (W.ι ≫ f) δ k α) =
      chowMk f δ k
        (@properPushforwardHom S B W.X X inferInstance inferInstance
          (W.ι ≫ f) inferInstance inferInstance f inferInstance inferInstance δ inferInstance
          W.ι (@Proper.of_isClosedImmersion S W.X X W.ι W.isClosedImmersion) rfl k α) :=
  @ChowGroup.properPushforward_chowMk S B W.X X inferInstance inferInstance
    (W.ι ≫ f) inferInstance inferInstance f inferInstance inferInstance δ inferInstance
    W.ι (@Proper.of_isClosedImmersion S W.X X W.ι W.isClosedImmersion) rfl k α

end AlgebraicGeometry.AlgebraicSpace.Hom
