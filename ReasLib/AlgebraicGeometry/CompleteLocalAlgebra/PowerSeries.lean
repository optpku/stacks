module

public import Mathlib.RingTheory.PowerSeries.Ideal
public import ReasLib.AlgebraicGeometry.CompleteLocalAlgebra.Basic
public import ReasLib.AlgebraicGeometry.Scheme.PowerSeries

/-! # The complete local power-series algebra -/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open AlgebraicGeometry.HomStack

noncomputable section

universe u

namespace PowerSeries

/-- The power-series ring over a field is complete for its maximal-adic topology. -/
instance instIsCompleteLocalRing {k : Type u} [Field k] :
    IsCompleteLocalRing (PowerSeries k) := sorry

end PowerSeries

namespace AlgebraicGeometry.CompleteLocalSAlgebra

/-- The residue-field morphism of the power-series ring over a field is locally
of finite type. -/
instance powerSeriesResidue_locallyOfFiniteType {k : Type u} [Field k] :
    LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal (PowerSeries k)))) ≫
        𝟙 (specPowerSeries k)) := sorry

/-- The power-series ring over a field, viewed as a complete local algebra over
its own spectrum with identity structure morphism. -/
def powerSeries (k : Type u) [Field k] : CompleteLocalSAlgebra (specPowerSeries k) :=
  CompleteLocalSAlgebra.of (PowerSeries k) (𝟙 (specPowerSeries k))
    powerSeriesResidue_locallyOfFiniteType

/-- The carrier of the identity power-series algebra is the power-series ring. -/
theorem powerSeries_carrier (k : Type u) [Field k] :
    (powerSeries k).carrier = PowerSeries k := rfl

/-- The structure morphism of the identity power-series algebra is the identity. -/
theorem powerSeries_toS (k : Type u) [Field k] :
    (powerSeries k).toS = 𝟙 (specPowerSeries k) := rfl

end AlgebraicGeometry.CompleteLocalSAlgebra
