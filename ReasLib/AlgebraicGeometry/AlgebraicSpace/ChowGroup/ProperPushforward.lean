/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.ProperPushforward

/-! # Proper pushforward on Chow groups of algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChowGroup

variable {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
  (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
  (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
  (δ : Points B → ℤ) [IsDimensionFunction δ]
  (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX) (k : ℤ)

/-- Proper pushforward of cycles carries rational boundaries to rational boundaries. -/
theorem properPushforward_mem_boundaries :
    RationalEquivalence.boundaries pX δ k ≤
      (RationalEquivalence.boundaries pY δ k).comap
        (Hom.properPushforwardHom pX pY δ f hf k) := sorry

/-- Proper pushforward on Chow groups is induced by the dimension-filtered cycle map. -/
def properPushforward : Hom.chowGroup pX δ k →+ Hom.chowGroup pY δ k :=
  QuotientAddGroup.map
    (RationalEquivalence.boundaries pX δ k) (RationalEquivalence.boundaries pY δ k)
    (Hom.properPushforwardHom pX pY δ f hf k)
    (properPushforward_mem_boundaries pX pY δ f hf k)

/-- Pushing forward the class of a cycle gives the class of its proper cycle pushforward. -/
theorem properPushforward_chowMk (α : Hom.cycleGroup pX δ k) :
    properPushforward pX pY δ f hf k (Hom.chowMk pX δ k α) =
      Hom.chowMk pY δ k (Hom.properPushforwardHom pX pY δ f hf k α) := sorry

end AlgebraicGeometry.AlgebraicSpace.ChowGroup
