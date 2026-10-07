module

public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin
public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.Divisor
import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.ClosedSubscheme

/-!
# Gysin homomorphisms and first Chern classes

This file compares pushforward after the Gysin homomorphism for a zero scheme with
intersection by the first Chern class of the defining invertible module.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Pushing the Gysin class of a cycle forward along the zero-scheme immersion equals
capping the cycle with the first Chern class of the defining invertible module. -/
theorem map_gysin_eq_firstChernClassCap
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (ℒ : X.Modules) [Invertible ℒ]
    (s : ℒ.sections) (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) (k + 1)) :
    ChowGroup.map δ (Over.mk (zeroSchemeι ℒ s ≫ p)) (Over.mk p)
        (Over.homMk (zeroSchemeι ℒ s) rfl :
          Over.mk (zeroSchemeι ℒ s ≫ p) ⟶ Over.mk p) k (gysin p δ ℒ s k α) =
      firstChernClassCap p δ ℒ k α := sorry

/-- Effective-Cartier intersection by the zero scheme of a section equals capping with
the first Chern class of its defining invertible module. -/
theorem cartierIntersection_eq_firstChernClassCap
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (ℒ : X.Modules) [Invertible ℒ]
    (s : ℒ.sections) [IsEffectiveCartierDivisor (zeroSchemeι ℒ s)] (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) (k + 1)) :
    cartierIntersection p δ ℒ s k α = firstChernClassCap p δ ℒ k α := sorry

/-- Pulling the relative divisor cycle of a nonzero meromorphic section back to an
effective Cartier zero scheme equals the first Chern class capped with its fundamental
cycle. -/
theorem gysin_relativeDivisorCycle_eq_firstChern_fundamental
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X]
    (ℒ : X.Modules) [Invertible ℒ] (s : ℒ.sections)
    [IsEffectiveCartierDivisor (zeroSchemeι ℒ s)]
    (𝒩 : X.Modules) [Invertible 𝒩]
    (t : X.toLocallyRingedSpace.meromorphicSections 𝒩) (ht : t ≠ 0)
    (k : ℤ)
    (hX : p.relativeDimensionFunction δ (genericPoint X) = (k + 1) + 1) :
    gysin p δ ℒ s k
        (MeromorphicSection.relativeDivisorCycle p δ 𝒩 t ht (k + 1) hX) =
      firstChernClassCap (zeroSchemeι ℒ s ≫ p) δ
        ((pullback (zeroSchemeι ℒ s)).obj 𝒩) k
        (@CycleGroup.fundamental (zeroScheme ℒ s)
          (@zeroSchemeIsLocallyNoetherian X
            (LocallyOfFiniteType.isLocallyNoetherian p) ℒ inferInstance s)
          ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) (k + 1)) := sorry

end AlgebraicGeometry.Scheme.Modules
