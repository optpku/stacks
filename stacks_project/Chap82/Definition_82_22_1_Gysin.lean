/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin

/-!
# Refined Gysin maps for zero schemes of invertible modules

The cycle argument-order interface for source statements specializes the
canonical locally finite refined-intersection construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
  (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
  (δ : Points B → ℤ) [IsDimensionFunction δ] (k : ℤ)
  (L : X.Modules) [isInvertibleObject L] (s : L.sections)

/-- Refined intersection of cycles, with the degree preceding the module and section. -/
abbrev gysinCycle (α : Function.locallyFinsupp (Points X) ℤ) :
    Function.locallyFinsupp (Points (zeroScheme L s).X) ℤ :=
  ChowGroup.RefinedGysin.cycle f δ L s k α

/-- Refined intersection sends degree-`k + 1` cycles to degree-`k` cycles. -/
theorem gysinCycle_mem (α : cycleGroup f δ (k + 1)) :
    gysinCycle f δ k L s (α : Function.locallyFinsupp (Points X) ℤ) ∈
      cycleGroup (zeroSchemeι L s ≫ f) δ k :=
  ChowGroup.RefinedGysin.cycle_mem f δ L s k α

end AlgebraicGeometry.AlgebraicSpace.Hom

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.gysinCycle :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ] (k : ℤ)
      (L : X.Modules) [isInvertibleObject L] (s : L.sections),
      Function.locallyFinsupp (Points X) ℤ →
        Function.locallyFinsupp (Points (zeroScheme L s).X) ℤ)

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.gysin :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ] (k : ℤ)
      (L : X.Modules) [isInvertibleObject L] (s : L.sections),
      Hom.cycleGroup f δ (k + 1) →+ Hom.chowGroup (zeroSchemeι L s ≫ f) δ k)

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.cartierIntersection :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ] (k : ℤ)
      (L : X.Modules) [isInvertibleObject L] (s : L.sections)
      [IsEffectiveCartierDivisor (zeroSchemeι L s)],
      Hom.cycleGroup f δ (k + 1) →+ Hom.chowGroup f δ k)
