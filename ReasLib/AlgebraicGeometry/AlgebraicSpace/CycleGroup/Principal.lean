/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Principal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.DeltaDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Irreducible
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.LocallyFiniteSum

/-! # Principal cycles on locally Noetherian integral algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function Set Topology TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The singleton cycles at generic points of prime divisors in a principal
Weil divisor form a locally finite family. -/
theorem principalCycle_locallyFinite {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsIntegral X] (φ : (RationalFunction X)ˣ) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      (@Function.locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _
        Z.genericPoint ((principalWeilDivisor X φ).coeff Z)).support :=
  sorry

/-- The ungraded principal divisor cycle of a rational unit, as the locally
finite sum of coefficient-weighted generic points of prime divisors. -/
noncomputable def principalCycle {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsIntegral X] (φ : (RationalFunction X)ˣ) :
    Function.locallyFinsupp (Points X) ℤ :=
  AlgebraicCycle.locallyFiniteSum
    (fun Z : PrimeDivisor X ↦
      @Function.locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _
        Z.genericPoint ((principalWeilDivisor X φ).coeff Z))
    (principalCycle_locallyFinite φ)

/-- The ungraded principal divisor cycle is the locally finite sum of its
prime-divisor singleton cycles. -/
theorem principalCycle_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsIntegral X] (φ : (RationalFunction X)ˣ) :
    principalCycle φ =
      AlgebraicCycle.locallyFiniteSum
        (fun Z : PrimeDivisor X ↦
          @Function.locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _
            Z.genericPoint ((principalWeilDivisor X φ).coeff Z))
        (principalCycle_locallyFinite φ) :=
  rfl

/-- If `dim_δ(Y) = k`, then the ungraded principal divisor cycle of `g` is a
`(k - 1)`-cycle on `Y`. -/
theorem principalCycle_mem {S : Scheme.{u}} {B Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ] [IsIntegral Y] (k : ℤ)
    (hY : closedSubspaceDeltaDimension pY δ (ClosedSubspace.id Y) = (k : EInt))
    (g : (RationalFunction Y)ˣ) :
    @principalCycle S Y (LocallyOfFiniteType.isLocallyNoetherian pY) inferInstance g ∈
      cycleGroup pY δ (k - 1) :=
  sorry

/-- At a prime divisor, the ungraded principal cycle has coefficient equal to
the order of vanishing of the rational unit. -/
theorem principalCycle_apply_primeDivisor {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsIntegral X] (φ : (RationalFunction X)ˣ)
    (Z : PrimeDivisor X) :
    principalCycle φ Z.genericPoint = Z.ord φ :=
  sorry

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
variable [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable [IsIntegral X]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]

/-- On an integral algebraic space of `δ`-dimension `n`, the principal cycle
of a rational unit is an `(n - 1)`-cycle. -/
theorem principalCycle_mem_of_deltaDimension (n : ℤ)
    (hX : deltaDimension f δ (univIrreducibleClosed X) = n)
    (φ : (RationalFunction X)ˣ) :
    @principalCycle S X (LocallyOfFiniteType.isLocallyNoetherian f) inferInstance φ ∈
      cycleGroup f δ (n - 1) :=
  sorry

/-- The principal divisor of a rational unit on an integral algebraic space
of `δ`-dimension `n`, regarded as an `(n - 1)`-cycle. -/
noncomputable def principalDivisor (n : ℤ)
    (hX : deltaDimension f δ (univIrreducibleClosed X) = n)
    (φ : (RationalFunction X)ˣ) : cycleGroup f δ (n - 1) :=
  ⟨@principalCycle S X (LocallyOfFiniteType.isLocallyNoetherian f) inferInstance φ,
    principalCycle_mem_of_deltaDimension f δ n hX φ⟩

/-- The underlying locally finite cycle of a principal divisor is the
canonical ungraded principal cycle. -/
theorem principalDivisor_coe (n : ℤ)
    (hX : deltaDimension f δ (univIrreducibleClosed X) = n)
    (φ : (RationalFunction X)ˣ) :
    (principalDivisor f δ n hX φ : Function.locallyFinsupp (Points X) ℤ) =
      @principalCycle S X (LocallyOfFiniteType.isLocallyNoetherian f) inferInstance φ :=
  rfl

/-- At a prime divisor, the principal divisor has coefficient equal to the
order of vanishing of the rational unit. -/
theorem principalDivisor_apply_primeDivisor (n : ℤ)
    (hX : deltaDimension f δ (univIrreducibleClosed X) = n)
    (φ : (RationalFunction X)ˣ) (Z : PrimeDivisor X) :
    (principalDivisor f δ n hX φ : Function.locallyFinsupp (Points X) ℤ)
        Z.genericPoint =
      (@PrimeDivisor.ord S X (LocallyOfFiniteType.isLocallyNoetherian f)
        inferInstance Z φ) :=
  @principalCycle_apply_primeDivisor S X
    (LocallyOfFiniteType.isLocallyNoetherian f) inferInstance φ Z

/-- The underlying cycle of a principal divisor belongs to the cycle group
in degree one less than the dimension of the space. -/
theorem principalDivisor_mem_cycleGroup (n : ℤ)
    (hX : deltaDimension f δ (univIrreducibleClosed X) = n)
    (φ : (RationalFunction X)ˣ) :
    (principalDivisor f δ n hX φ : Function.locallyFinsupp (Points X) ℤ) ∈
      cycleGroup f δ (n - 1) :=
  (principalDivisor f δ n hX φ).property

end AlgebraicGeometry.AlgebraicSpace.Hom
