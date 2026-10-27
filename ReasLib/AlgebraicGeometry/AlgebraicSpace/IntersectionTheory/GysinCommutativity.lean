/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.ZeroSection.Interchange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.ProperPushforward

/-!
# Commutativity of refined Gysin maps

The construction uses Chow groups of good algebraic spaces over a base with a
dimension function. Extension to more general geometric settings requires the
corresponding cycle and rational-equivalence theories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.DoubleZero

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Refined Gysin homomorphisms associated to two invertible-module sections
commute after the canonical interchange of their iterated zero schemes. -/
theorem chowGysin_comm {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (L L' : X.Modules) [isInvertibleObject L] [isInvertibleObject L']
    (s : L.sections) (s' : L'.sections) (k : ℤ) :
    (ChowGroup.RefinedGysin.gysin (zeroSchemeι L s ≫ f) δ
        ((Modules.pullback (zeroSchemeι L s)).obj L')
        (Modules.sectionsPullback (zeroSchemeι L s) L' s') k).comp
      (ChowGroup.RefinedGysin.gysin f δ L s (k + 1)) =
    (ChowGroup.properPushforward
        ((iterate L' L s' s).ι ≫ zeroSchemeι L' s' ≫ f)
        ((iterate L L' s s').ι ≫ zeroSchemeι L s ≫ f) δ
        (swapIso L L' s s').hom
        (swapIso_hom_comp_structure f L L' s s') k).comp
      ((ChowGroup.RefinedGysin.gysin (zeroSchemeι L' s' ≫ f) δ
          ((Modules.pullback (zeroSchemeι L' s')).obj L)
          (Modules.sectionsPullback (zeroSchemeι L' s') L s) k).comp
        (ChowGroup.RefinedGysin.gysin f δ L' s' (k + 1))) :=
  sorry

/-- Pointwise form of refined Gysin commutativity on a Chow class. -/
theorem chowGysin_comm_apply {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (L L' : X.Modules) [isInvertibleObject L] [isInvertibleObject L']
    (s : L.sections) (s' : L'.sections) (k : ℤ)
    (α : chowGroup f δ (k + 1 + 1)) :
    ChowGroup.RefinedGysin.gysin (zeroSchemeι L s ≫ f) δ
        ((Modules.pullback (zeroSchemeι L s)).obj L')
        (Modules.sectionsPullback (zeroSchemeι L s) L' s') k
      (ChowGroup.RefinedGysin.gysin f δ L s (k + 1) α) =
    ChowGroup.properPushforward
        ((iterate L' L s' s).ι ≫ zeroSchemeι L' s' ≫ f)
        ((iterate L L' s s').ι ≫ zeroSchemeι L s ≫ f) δ
        (swapIso L L' s s').hom
        (swapIso_hom_comp_structure f L L' s s') k
      (ChowGroup.RefinedGysin.gysin (zeroSchemeι L' s' ≫ f) δ
        ((Modules.pullback (zeroSchemeι L' s')).obj L)
        (Modules.sectionsPullback (zeroSchemeι L' s') L s) k
        (ChowGroup.RefinedGysin.gysin f δ L' s' (k + 1) α)) := by
  exact DFunLike.congr_fun (chowGysin_comm f δ L L' s s' k) α

end AlgebraicGeometry.AlgebraicSpace.Hom
