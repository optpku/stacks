/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.WeilDivisor
public import stacks_project.Chap72.Lemma_72_7_3_Quotient

/-!
# Weil divisors as δ-dimension cycles

A Weil divisor on a decent algebraic space determines a locally finite cycle on
`|X|` by placing each coefficient at the generic point of the corresponding
prime divisor. In the good integral setup of Situation 82.2.1 this cycle lies
in `Z_{n-1}(X)`, and the divisor of a regular meromorphic section of an
invertible module is the resulting `(n-1)`-cycle.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open Function Set Topology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace WeilDivisor

variable {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]

#check (AlgebraicGeometry.AlgebraicSpace.WeilDivisor.toCycle_apply :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] (D : WeilDivisor X) (x : Points X),
    toCycle D x =
      ∑ᶠ Z : PrimeDivisor X,
        (@Function.locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _
          Z.genericPoint (D.coeff Z)) x)

end WeilDivisor

namespace Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable [IsIntegral X]

#check (AlgebraicGeometry.AlgebraicSpace.Hom.meromorphicSectionDivisorCycle_mem :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
    [IsDimensionFunction δ] [IsIntegral X] {L : X.Modules}
    [isInvertibleObject L] (s : meromorphicSections X L)
    (hs : IsRegularMeromorphicSection X L s),
    meromorphicSectionDivisorCycle f δ s hs ∈
      cycleGroup f δ (deltaDimension f δ (univIrreducibleClosed X) - 1))

end Hom

end AlgebraicGeometry.AlgebraicSpace
