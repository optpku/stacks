/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.ValuationRing
import StacksCheckRecall

/-!
# Lemma 71.8.5

Effective Cartier divisors on the generic fiber of a smooth algebraic space over
a valuation ring extend to effective Cartier divisors on the total space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 71.8.5 -/
@[stacks 0DMC] #check
  (AlgebraicGeometry.AlgebraicSpace.IsEffectiveCartierDivisor.exists_of_genericFiber :
    ∀ {R K : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
      [Field K] [Algebra R K] [IsFractionRing R K]
      {X : AlgebraicSpace (Spec (CommRingCat.of R))}
      (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) [Smooth f]
      (D : ClosedSubspace (GenericFiber.baseChange R K X))
      [IsEffectiveCartierDivisor D.ι],
      ∃ D' : ClosedSubspace X,
        IsEffectiveCartierDivisor D'.ι ∧
          (D'.inverseImageSubspace (GenericFiber.toSource R K X)).idealSheaf =
            D.idealSheaf)

#check
  (AlgebraicGeometry.AlgebraicSpace.IsEffectiveCartierDivisor.exists_of_genericFiber_overIso :
    ∀ {R K : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
      [Field K] [Algebra R K] [IsFractionRing R K]
      {X : AlgebraicSpace (Spec (CommRingCat.of R))}
      (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) [Smooth f]
      (D : ClosedSubspace (GenericFiber.baseChange R K X))
      [IsEffectiveCartierDivisor D.ι],
      ∃ D' : ClosedSubspace X,
        IsEffectiveCartierDivisor D'.ι ∧
          Nonempty
            (Over.mk (D'.inverseImageSubspace (GenericFiber.toSource R K X)).ι ≅
              Over.mk D.ι))

end AlgebraicGeometry.AlgebraicSpace
