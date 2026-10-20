/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.RegularSection.Tensor
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.StructureSheafCycle
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Coherent

/-!
# Gysin pullback of associated cycles

This file compares Gysin pullback along the zero scheme of a section with associated cycles of
coherent modules and cycles of closed subschemes.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- If multiplication by a section is injective on a coherent module, Gysin pullback of its
degree-`k + 1` associated cycle is the degree-`k` associated cycle of its pullback to the zero
scheme. -/
theorem gysin_associatedCycle
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (ℒ : X.Modules) [Invertible ℒ] (s : ℒ.sections)
    (ℱ : X.Modules) [ℱ.IsCoherent] (k : ℤ)
    (hℱ : ∀ x ∈ RingedSpace.moduleSupport ℱ,
      p.relativeDimensionFunction δ x ≤ k + 1)
    [Mono (RingedSpace.tensorSectionHom ℱ ℒ s)] :
    gysin p δ ℒ s k
        ⟨@associatedCycle X (LocallyOfFiniteType.isLocallyNoetherian p) ℱ inferInstance
            (p.relativeDimensionFunction δ) (k + 1),
          @associatedCycle_mem_dimensionSubgroup X
            (LocallyOfFiniteType.isLocallyNoetherian p) ℱ inferInstance
            (p.relativeDimensionFunction δ) (k + 1)⟩ =
      @chowClass (zeroScheme ℒ s)
        (@zeroSchemeIsLocallyNoetherian X
          (LocallyOfFiniteType.isLocallyNoetherian p) ℒ inferInstance s)
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) inferInstance k
        ⟨@associatedCycle (zeroScheme ℒ s)
            (@zeroSchemeIsLocallyNoetherian X
              (LocallyOfFiniteType.isLocallyNoetherian p) ℒ inferInstance s)
            ((pullback (zeroSchemeι ℒ s)).obj ℱ)
            (@pullback_isCoherent (zeroScheme ℒ s) X
              (@zeroSchemeIsLocallyNoetherian X
                (LocallyOfFiniteType.isLocallyNoetherian p) ℒ inferInstance s)
              (LocallyOfFiniteType.isLocallyNoetherian p) (zeroSchemeι ℒ s) ℱ inferInstance)
            ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k,
          @associatedCycle_mem_dimensionSubgroup (zeroScheme ℒ s)
            (@zeroSchemeIsLocallyNoetherian X
              (LocallyOfFiniteType.isLocallyNoetherian p) ℒ inferInstance s)
            ((pullback (zeroSchemeι ℒ s)).obj ℱ)
            (@pullback_isCoherent (zeroScheme ℒ s) X
              (@zeroSchemeIsLocallyNoetherian X
                (LocallyOfFiniteType.isLocallyNoetherian p) ℒ inferInstance s)
              (LocallyOfFiniteType.isLocallyNoetherian p) (zeroSchemeι ℒ s) ℱ inferInstance)
            ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k⟩ := sorry

/-- Gysin pullback of the degree-`k + 1` cycle of a closed subscheme is the degree-`k` cycle of
its scheme-theoretic intersection with the zero scheme when that intersection is an effective
Cartier divisor. -/
theorem gysin_closedSubschemeCycle
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (ℒ : X.Modules) [Invertible ℒ] (s : ℒ.sections)
    (Z : X.IdealSheafData) (k : ℤ)
    (hZ : p.closedSubschemeDeltaDimension δ Z ≤ ((k + 1 : ℤ) : EInt))
    [IsEffectiveCartierDivisor
      (((zeroIdealSheaf ℒ s).comap Z.subschemeι).subschemeι)] :
    gysin p δ ℒ s k (p.closedSubschemeCycle δ Z (k + 1) hZ) =
      @chowClass (zeroScheme ℒ s)
        (@zeroSchemeIsLocallyNoetherian X
          (LocallyOfFiniteType.isLocallyNoetherian p) ℒ inferInstance s)
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) inferInstance k
        (@Scheme.IdealSheafData.associatedCycle (zeroScheme ℒ s)
          (@zeroSchemeIsLocallyNoetherian X
            (LocallyOfFiniteType.isLocallyNoetherian p) ℒ inferInstance s)
          (Z.comap (zeroSchemeι ℒ s))
          ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k) := sorry

end AlgebraicGeometry.Scheme.Modules
