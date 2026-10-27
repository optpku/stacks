/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Numerical.Immersion
import StacksCheckRecall

/-! # Remark 108.5.9 (Numerical invariants)

The numerical Quot locus is the pullback of the numerical coherent-sheaf substack.
It is an algebraic space, and its inclusion is flat and closed. The three
independent openness conditions are finite indexing, a locally Noetherian base,
and the family of all integral powers of an invertible module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}
variable (f : X ⟶ B) [FinitePresentation f] [Separated f]
variable (F : X.Modules) [F.IsQuasicoherent] {I : Type u}
variable (E : I → ModuleDerived X) (P : I → ℤ) (hE : ∀ i, ModuleDerived.IsPerfect (E i))

/- Remark 108.5.9 (Numerical invariants) (1) -/
@[stacks 0DP6] #check (AlgebraicGeometry.AlgebraicSpace.Quot.forgetCoh f F :
  (quot f F).Elementsᵒᵖ ⥤ CohStack.Obj f)

/- Remark 108.5.9 (Numerical invariants) (2) -/
@[stacks 0DP6] #check (AlgebraicGeometry.AlgebraicSpace.Quot.quotNumericalSquare f F E P hE :
  CategoricalPullback.CatCommSqOver (forgetCoh f F) (CohStack.numerical f E P).ι
    ((quotNumerical f F E P hE).toFunctor.Elementsᵒᵖ))

/- Remark 108.5.9 (Numerical invariants) (3) -/
@[stacks 0DP6] #check (AlgebraicGeometry.AlgebraicSpace.Quot.quotNumericalSquare_comparison_isEquivalence f F E P hE :
  (quotNumericalSquare f F E P hE).comparison.IsEquivalence)

/- Remark 108.5.9 (Numerical invariants) (4) -/
@[stacks 0DP6] #check (AlgebraicGeometry.AlgebraicSpace.Quot.quotNumerical_isAlgebraicSpaceOver f F E P hE :
  IsAlgebraicSpaceOver (quotNumerical f F E P hE).toFunctor)

/- Remark 108.5.9 (Numerical invariants) (5) -/
@[stacks 0DP6] #check (AlgebraicGeometry.AlgebraicSpace.Quot.isClosedImmersion_quotNumericalι f F E P hE :
  SchemeOver.IsClosedImmersion (quotNumericalι f F E P hE))

/- Remark 108.5.9 (Numerical invariants) (6) -/
@[stacks 0DP6] #check (AlgebraicGeometry.AlgebraicSpace.Quot.isFlat_quotNumericalι f F E P hE :
  SchemeOver.IsFlat (quotNumericalι f F E P hE))

section FiniteIndex

variable [Finite I]

/- Remark 108.5.9 (Numerical invariants) (7) -/
@[stacks 0DP6] #check (AlgebraicGeometry.AlgebraicSpace.Quot.isOpenImmersion_quotNumericalι_of_finite f F E P hE :
  IsOpenImmersionOnSchemesOver (quotNumericalι f F E P hE))

end FiniteIndex

section NoetherianBase

variable [AlgebraicSpace.IsLocallyNoetherian B]

/- Remark 108.5.9 (Numerical invariants) (8) -/
@[stacks 0DP6] #check (AlgebraicGeometry.AlgebraicSpace.Quot.isOpenImmersion_quotNumericalι_of_locallyNoetherian f F E P hE :
  IsOpenImmersionOnSchemesOver (quotNumericalι f F E P hE))

end NoetherianBase

variable (L : X.Modules) [isInvertibleObject L] (Pℤ : ℤ → ℤ)

/- Remark 108.5.9 (Numerical invariants) (9) -/
@[stacks 0DP6] #check (AlgebraicGeometry.AlgebraicSpace.Quot.isOpenImmersion_quotNumericalHilbertι f F L Pℤ :
  IsOpenImmersionOnSchemesOver
    (quotNumericalι f F (invertiblePowerFamily L)
      (fun n : ULift.{u, 0} ℤ ↦ Pℤ n.down) (isPerfect_invertiblePowerFamily L)))

end AlgebraicGeometry.AlgebraicSpace.Quot
