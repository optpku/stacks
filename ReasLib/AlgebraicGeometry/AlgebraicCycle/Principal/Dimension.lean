/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Principal
public import ReasLib.AlgebraicGeometry.CycleGroup
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Dimension

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicCycle

/-- The principal algebraic cycle on an integral scheme of `δ`-dimension `n` is supported in
`δ`-dimension `n - 1`. -/
theorem principal_mem_dimensionSubgroup
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] [IsIntegral X] (n : ℤ)
    (hX : p.relativeDimensionFunction δ (genericPoint X) = n)
    (f : X.functionFieldˣ) :
    @principal X (LocallyOfFiniteType.isLocallyNoetherian p) inferInstance f ∈
      dimensionSubgroup (p.relativeDimensionFunction δ) (n - 1) := sorry

end AlgebraicGeometry.AlgebraicCycle

namespace AlgebraicGeometry.Scheme.Hom

/-- The principal divisor of a function-field unit on an integral scheme of `δ`-dimension
`n`, regarded as a cycle of dimension `n - 1`. -/
noncomputable def principalDivisor
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] [IsIntegral X] (n : ℤ)
    (hX : p.relativeDimensionFunction δ (genericPoint X) = n)
    (f : X.functionFieldˣ) :
    AlgebraicGeometry.CycleGroup X (p.relativeDimensionFunction δ) (n - 1) :=
  ⟨@AlgebraicCycle.principal X (LocallyOfFiniteType.isLocallyNoetherian p) inferInstance f,
    AlgebraicCycle.principal_mem_dimensionSubgroup δ p n hX f⟩

/-- The coefficient of a principal divisor cycle is its order of vanishing. -/
theorem principalDivisor_apply
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] [IsIntegral X] (n : ℤ)
    (hX : p.relativeDimensionFunction δ (genericPoint X) = n)
    (f : X.functionFieldˣ) (x : X) :
    AlgebraicGeometry.CycleGroup.toAlgebraicCycle
        (p.relativeDimensionFunction δ) (n - 1) (principalDivisor δ p n hX f) x =
      @Scheme.ord X inferInstance (LocallyOfFiniteType.isLocallyNoetherian p) f x := sorry

/-- At a prime divisor, the principal divisor cycle has the coefficient of the canonical
principal Weil divisor. -/
theorem principalDivisor_apply_primeDivisor
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] [IsIntegral X] (n : ℤ)
    (hX : p.relativeDimensionFunction δ (genericPoint X) = n)
    (f : X.functionFieldˣ) (Z : PrimeDivisor X) :
    AlgebraicGeometry.CycleGroup.toAlgebraicCycle
        (p.relativeDimensionFunction δ) (n - 1) (principalDivisor δ p n hX f)
        Z.genericPoint =
      (@Scheme.principalWeilDivisor X (LocallyOfFiniteType.isLocallyNoetherian p)
        inferInstance f).coeff Z := sorry

end AlgebraicGeometry.Scheme.Hom
