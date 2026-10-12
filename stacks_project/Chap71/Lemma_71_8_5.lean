/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Valuation.ValuationRing
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap71.Definition_71_6_1_EffectiveCartier
public import stacks_project.Chap71.Lemma_71_6_12_Pullback
public import stacks_project.Chap71.Lemma_71_8_5_GenericFiber

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

/-- Lemma 71.8.5: Let `R` be a valuation ring with fraction field `K`. Let `X` be
an algebraic space over `R` such that `X ⟶ Spec (CommRingCat.of R)` is smooth.
For every effective Cartier divisor `D` on `GenericFiber.baseChange R K X` there
exists an effective Cartier divisor `D'` on `X` whose inverse image along
`GenericFiber.toSource R K X` has the same ideal sheaf as `D`. -/
@[stacks 0DMC]
theorem IsEffectiveCartierDivisor.exists_of_genericFiber
    {R K : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X : AlgebraicSpace (Spec (CommRingCat.of R))}
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) [Smooth f]
    (D : ClosedSubspace (GenericFiber.baseChange R K X))
    [IsEffectiveCartierDivisor D.ι] :
    ∃ D' : ClosedSubspace X,
      IsEffectiveCartierDivisor D'.ι ∧
        (D'.inverseImage (GenericFiber.toSource R K X)).idealSheaf = D.idealSheaf :=
  sorry

/-- An extension of an effective Cartier divisor from the generic fiber is
isomorphic over the generic fiber to the original divisor. -/
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
          (Over.mk (D'.inverseImage (GenericFiber.toSource R K X)).ι ≅
            Over.mk D.ι) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
