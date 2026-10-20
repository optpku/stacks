module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GenericFiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Ideal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier

/-!
# Effective Cartier divisors over valuation rings

Effective Cartier divisors on the generic fiber of a smooth algebraic space
over a valuation ring extend to the total space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every effective Cartier divisor on the generic fiber of a smooth algebraic
space over a valuation ring extends to an effective Cartier divisor on the
total space with the same ideal sheaf after restriction. -/
theorem IsEffectiveCartierDivisor.exists_of_genericFiber
    {R K : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X : AlgebraicSpace (Spec (CommRingCat.of R))}
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) [Smooth f]
    (D : ClosedSubspace (GenericFiber.baseChange R K X))
    [IsEffectiveCartierDivisor D.ι] :
    ∃ D' : ClosedSubspace X,
      IsEffectiveCartierDivisor D'.ι ∧
        (D'.inverseImageSubspace (GenericFiber.toSource R K X)).idealSheaf =
          D.idealSheaf :=
  sorry

/-- Every effective Cartier divisor on the generic fiber of a smooth algebraic
space over a valuation ring extends to a divisor isomorphic to it over the
generic fiber. -/
theorem IsEffectiveCartierDivisor.exists_of_genericFiber_overIso
    {R K : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X : AlgebraicSpace (Spec (CommRingCat.of R))}
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) [Smooth f]
    (D : ClosedSubspace (GenericFiber.baseChange R K X))
    [IsEffectiveCartierDivisor D.ι] :
    ∃ D' : ClosedSubspace X,
      IsEffectiveCartierDivisor D'.ι ∧
        Nonempty
          (Over.mk (D'.inverseImageSubspace (GenericFiber.toSource R K X)).ι ≅
            Over.mk D.ι) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
