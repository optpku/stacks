/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.FirstChernFundamental

/-!
# Codimension-one Chow groups of good integral algebraic spaces

The divisor of a regular meromorphic section of an invertible module defines
a section-independent class in the canonical Chow group in degree `dim_δ(X) - 1`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Hom.codimOneCycleGroup :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
    [IsDimensionFunction δ] [IsIntegral X],
    AddSubgroup (Function.locallyFinsupp (Points X) ℤ))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.codimOneChowGroup :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
    [IsDimensionFunction δ] [IsIntegral X], Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.chowClass :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
    [IsDimensionFunction δ] [IsIntegral X] (α : Function.locallyFinsupp (Points X) ℤ),
    Hom.codimOneChowGroup f δ)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.chowClass_eq_mk :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
    [IsDimensionFunction δ] [IsIntegral X] (α : Function.locallyFinsupp (Points X) ℤ)
    (hα : α ∈ Hom.codimOneCycleGroup f δ),
    Hom.chowClass f δ α =
      Hom.chowMk f δ (Hom.deltaDimension f δ (univIrreducibleClosed X) - 1) ⟨α, hα⟩)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.firstChernCapFundamental :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
    [IsDimensionFunction δ] [IsIntegral X] (L : X.Modules) [isInvertibleObject L],
    Hom.codimOneChowGroup f δ)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.meromorphicSectionDivisorCycle_chowClass_eq :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
    [IsDimensionFunction δ] [IsIntegral X] {L : X.Modules}
    [isInvertibleObject L] (s t : meromorphicSections X L)
    (hs : IsRegularMeromorphicSection X L s) (ht : IsRegularMeromorphicSection X L t),
    Hom.chowClass f δ (Hom.meromorphicSectionDivisorCycle f δ s hs) =
      Hom.chowClass f δ (Hom.meromorphicSectionDivisorCycle f δ t ht))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.firstChernCapFundamental_eq :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
    [IsDimensionFunction δ] [IsIntegral X] (L : X.Modules) [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s),
    Hom.firstChernCapFundamental f δ L =
      Hom.chowClass f δ (Hom.meromorphicSectionDivisorCycle f δ s hs))
