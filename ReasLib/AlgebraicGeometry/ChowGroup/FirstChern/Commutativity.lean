module

public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.Pushforward
public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.Relative
public import ReasLib.AlgebraicGeometry.ChowGroup.KeyFormula

/-!
# Commutativity of first-Chern intersections

This file records the symmetry of intersection by the first Chern classes of two
invertible modules, both on relative Chow groups and on relative divisor cycles.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Intersecting the relative divisor cycle of either of two nonzero meromorphic sections
with the first Chern class of the other invertible module gives the same Chow class. -/
theorem firstChernClassCap_relativeDivisorCycle_comm
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X] (k : ℤ)
    (hX : p.relativeDimensionFunction δ (genericPoint X) = (k + 1) + 1)
    (ℒ 𝒩 : X.Modules) [Invertible ℒ] [Invertible 𝒩]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (t : X.toLocallyRingedSpace.meromorphicSections 𝒩) (hs : s ≠ 0) (ht : t ≠ 0) :
    firstChernClassCap p δ 𝒩 k
        (MeromorphicSection.relativeDivisorCycle p δ ℒ s hs (k + 1) hX) =
      firstChernClassCap p δ ℒ k
        (MeromorphicSection.relativeDivisorCycle p δ 𝒩 t ht (k + 1) hX) := sorry

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ChowGroup

/-- Intersection by the first Chern classes of two invertible modules commutes on
relative Chow groups. -/
theorem firstChernClassCap_comm
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (ℒ 𝒩 : X.left.Modules) [Scheme.Modules.Invertible ℒ]
    [Scheme.Modules.Invertible 𝒩] (k : ℤ) (α : RelativeChow δ X (k + 2)) :
    firstChernClassCap δ X ℒ ((k + 2) - 1)
        (firstChernClassCap δ X 𝒩 (k + 2) α) =
      firstChernClassCap δ X 𝒩 ((k + 2) - 1)
        (firstChernClassCap δ X ℒ (k + 2) α) := sorry

end AlgebraicGeometry.ChowGroup
