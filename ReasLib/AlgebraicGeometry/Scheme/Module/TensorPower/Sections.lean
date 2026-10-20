module

public import Mathlib.Algebra.DirectSum.Module
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower

/-!
# Graded sections of integral tensor powers

This leaf owns the direct-sum carriers formed from degree-zero cohomology of
integral tensor powers of an invertible scheme module. It does not choose a
multiplication or module action; applications supply those structures when the
relevant graded comparison maps have been constructed. Its additive structures
and degree inclusions are those of the standard direct sums, so downstream
constructions can use the ordinary `DirectSum` API directly.
-/

@[expose] public section

open CategoryTheory
open TopologicalSpace
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.TensorPower

variable {X : Scheme.{u}}
variable [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/-- The nonnegative graded carrier formed from global sections of integral tensor powers. -/
abbrev gradedSections
    (L : X.Modules) [Invertible L] : Type u :=
  DirectSum ℕ fun d ↦
    (RingedSpace.moduleCohomology (tensorPowerInt L (d : ℤ)) 0 : Type u)

/-- The graded carrier of sections of twists of `F` by tensor powers of `L` in degrees at least
`k`. -/
abbrev twistedSectionsFrom
    (L F : X.Modules) [Invertible L] (k : ℤ) : Type u :=
  DirectSum {d : ℤ // k ≤ d} fun d ↦
    (RingedSpace.moduleCohomology (twistByTensorPower L F d.1) 0 : Type u)

end AlgebraicGeometry.Scheme.Modules.TensorPower
