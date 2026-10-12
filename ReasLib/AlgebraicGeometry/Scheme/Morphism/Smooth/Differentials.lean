/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension
import Mathlib.Tactic.CrossRefAttribute

/-!
# Differentials of Smooth Scheme Morphisms

The sheaf of relative differentials of a smooth morphism is finite locally free. Conversely, a
locally finite type morphism with locally free relative differentials is smooth over a field of
characteristic zero, or over a perfect field when its source is reduced. The rank of the
differentials at a point agrees with the local dimension of the corresponding fiber.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- Smoothness gives the sheaf of relative differentials its canonical finite locally free
instance. -/
instance instIsFiniteLocallyFreeDifferentialsOfSmooth
    (f : X ⟶ S) [Smooth f] :
    (Ω[f.toShHom]).IsFiniteLocallyFree := by
  sorry

/-- A locally finite type morphism to the spectrum of a characteristic-zero field is smooth when
its sheaf of relative differentials is locally free. -/
instance instSmoothOfCharZeroOfIsLocallyFreeDifferentials
    {k : Type u} [Field k] [CharZero k] (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f]
    [(Ω[f.toShHom]).IsLocallyFree] :
    Smooth f := sorry

/-- A locally finite type morphism from a reduced scheme to the spectrum of a perfect field is
smooth when its sheaf of relative differentials is locally free. -/
instance instSmoothOfPerfectFieldOfIsReducedOfIsLocallyFreeDifferentials
    {k : Type u} [Field k] [PerfectField k] (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [IsReduced X]
    [(Ω[f.toShHom]).IsLocallyFree] :
    Smooth f := sorry

/-- The relative differentials of a smooth morphism are finite locally free. -/
@[stacks 02G1 "(1)"]
theorem Smooth.differentials_isFiniteLocallyFree
    (f : X ⟶ S) (hf : Smooth f) :
    (Ω[f.toShHom]).IsFiniteLocallyFree := by
  exact @instIsFiniteLocallyFreeDifferentialsOfSmooth _ _ f hf

/-- The rank of the relative differentials of a smooth morphism equals its fiber dimension. -/
@[stacks 02G1 "(2)"]
theorem Smooth.rankAtClosedPoint_differentials_eq_fiberDimensionAt
    (f : X ⟶ S) (hf : Smooth f) (x : X) :
    (Module.rankAtStalk
      (RingedSpace.stalkModuleCat (Ω[f.toShHom]) x)
      (IsLocalRing.closedPoint (X.presheaf.stalk x)) : WithBot ℕ∞) =
      f.fiberDimensionAt x := by
  sorry

end AlgebraicGeometry
