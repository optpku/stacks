/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.LocallyFinsupp
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.LocallyFiniteSum
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.MeromorphicSection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Principal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Dimension


/-!
# Weil divisors as δ-dimension cycles

A Weil divisor on a decent algebraic space determines a locally finite cycle on
`|X|` by placing each coefficient at the generic point of the corresponding
prime divisor. For a good integral space this cycle lies
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

/-- The singleton cycles at the generic points of the prime divisors occurring
in a Weil divisor form a locally finite family on `|X|`. -/
theorem genericPointTermsLocallyFinite (D : WeilDivisor X) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      (@Function.locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _
        Z.genericPoint (D.coeff Z)).support := sorry

/-- Regard a Weil divisor as the locally finite cycle carrying its coefficient
at the generic point of each prime divisor. -/
noncomputable def toCycle (D : WeilDivisor X) :
    Function.locallyFinsupp (Points X) ℤ :=
  AlgebraicCycle.locallyFiniteSum
    (fun Z : PrimeDivisor X ↦
      @Function.locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _
        Z.genericPoint (D.coeff Z))
    (genericPointTermsLocallyFinite D)

/-- The coefficient of the cycle of a Weil divisor is the locally finite sum of
its prime-divisor singleton cycles at the given point. -/
theorem toCycle_apply (D : WeilDivisor X) (x : Points X) :
    toCycle D x =
      ∑ᶠ Z : PrimeDivisor X,
        (@Function.locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _
          Z.genericPoint (D.coeff Z)) x := sorry

/-- The cycle of a Weil divisor is the locally finite sum of its prime-divisor
singleton cycles. -/
theorem toCycle_eq_finsum_single (D : WeilDivisor X) :
    toCycle D =
      AlgebraicCycle.locallyFiniteSum
        (fun Z : PrimeDivisor X ↦
          @Function.locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _
            Z.genericPoint (D.coeff Z))
        (genericPointTermsLocallyFinite D) := sorry

/-- Conversion of Weil divisors to cycles is additive. -/
theorem toCycle_add (D E : WeilDivisor X) :
    toCycle (D + E) = toCycle D + toCycle E := sorry

end WeilDivisor

namespace WeilDivisor

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable [IsLocallyNoetherian X] [IsIntegral X]

/-- The cycle of a principal Weil divisor is the locally finite sum of the
orders of its rational unit at generic points of prime divisors. -/
theorem toCycle_ofRationalUnit (φ : (RationalFunction X)ˣ) (x : Points X) :
    toCycle (principalWeilDivisor X φ) x =
      ∑ᶠ Z : PrimeDivisor X,
        (@Function.locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _
          Z.genericPoint (Z.ord φ)) x := sorry

end WeilDivisor

namespace Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable [IsIntegral X]

/-- On a good integral algebraic space, the cycle of a Weil divisor is an
`(n-1)`-cycle, where `n = dim_δ(X)`. -/
theorem toCycle_mem_cycleGroup (D : WeilDivisor X) :
    WeilDivisor.toCycle D ∈
      cycleGroup f δ (deltaDimension f δ (univIrreducibleClosed X) - 1) := sorry

/-- The `(n-1)`-cycle `div_L(s)` associated to a nonzero meromorphic section of
an invertible module, obtained by converting its Weil divisor. The dimension function `δ` records the ambient
grading `Z_{n-1}(X)`. -/
noncomputable def meromorphicSectionDivisorCycle {L : X.Modules}
    [isInvertibleObject L] (s : meromorphicSections X L)
    (hs : IsRegularMeromorphicSection X L s) :
    Function.locallyFinsupp (Points X) ℤ :=
  let _ := δ
  let _ := ‹IsQuasiSeparated B›
  let _ := ‹QuasiSeparated f›
  let _ := ‹IsDimensionFunction δ›
  WeilDivisor.toCycle
    (@nonzeroMeromorphicSectionWeilDivisor S X
      (LocallyOfFiniteType.isLocallyNoetherian f) inferInstance L inferInstance s hs)

/-- The meromorphic-section divisor cycle is the Weil-divisor conversion of
`nonzeroMeromorphicSectionWeilDivisor`. -/
theorem meromorphicSectionDivisorCycle_def {L : X.Modules}
    [isInvertibleObject L] (s : meromorphicSections X L)
    (hs : IsRegularMeromorphicSection X L s) :
    meromorphicSectionDivisorCycle f δ s hs =
      WeilDivisor.toCycle
        (@nonzeroMeromorphicSectionWeilDivisor S X
          (LocallyOfFiniteType.isLocallyNoetherian f) inferInstance L inferInstance
          s hs) := sorry

/-- Coefficients of `div_L(s)` are the locally finite sum of `ord_{Z, L}(s)` at
generic points of prime divisors. -/
theorem meromorphicSectionDivisorCycle_apply {L : X.Modules}
    [isInvertibleObject L] (s : meromorphicSections X L)
    (hs : IsRegularMeromorphicSection X L s) (x : Points X) :
    meromorphicSectionDivisorCycle f δ s hs x =
      ∑ᶠ Z : PrimeDivisor X,
        (@Function.locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _
          Z.genericPoint
          (MeromorphicSection.ord s hs Z)) x := sorry

/-- The divisor cycle of a nonzero meromorphic section is an `(n-1)`-cycle. -/
theorem meromorphicSectionDivisorCycle_mem {L : X.Modules}
    [isInvertibleObject L] (s : meromorphicSections X L)
    (hs : IsRegularMeromorphicSection X L s) :
    meromorphicSectionDivisorCycle f δ s hs ∈
      cycleGroup f δ (deltaDimension f δ (univIrreducibleClosed X) - 1) := sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
