/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.MorphismAlgebraization

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe u

/- Lemma 30.28.3: A compatible system of morphisms on adic stages over a complete
Noetherian affine base algebraizes uniquely when the source is proper and the target
is separated of finite type. -/
@[stacks 0A42] #check (AlgebraicGeometry.Scheme.existsUnique_algebraizingHom :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of A))
    (fY : Y ⟶ Spec (CommRingCat.of A))
    [IsProper fX] [IsSeparated fY] [Scheme.Hom.FiniteType fY]
    (g : ∀ n : ℕ+, AdicThickening.stage fX I n ⟶ AdicThickening.stage fY I n)
    (_ : ∀ n, g n ≫ AdicThickening.toSpec fY I n = AdicThickening.toSpec fX I n)
    (_ : ∀ n,
      g n ≫ AdicThickening.transition fY I n =
        AdicThickening.transition fX I n ≫ g (n + 1)),
    ∃! G : X ⟶ Y, G ≫ fY = fX ∧
      ∀ n, g n ≫ AdicThickening.ι fY I n = AdicThickening.ι fX I n ≫ G)

#check (AlgebraicGeometry.Scheme.hom_ext_of_forall_stageMap :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of A))
    (fY : Y ⟶ Spec (CommRingCat.of A))
    [IsProper fX] [IsSeparated fY] [Scheme.Hom.FiniteType fY]
    {G₁ G₂ : X ⟶ Y} (h₁ : G₁ ≫ fY = fX) (h₂ : G₂ ≫ fY = fX)
    (_ : ∀ n, AdicThickening.stageMap fX fY I G₁ h₁ n =
      AdicThickening.stageMap fX fY I G₂ h₂ n),
    G₁ = G₂)
