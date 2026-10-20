module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Principal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.DeltaDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.Noetherian
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


end AlgebraicGeometry.AlgebraicSpace.Hom
