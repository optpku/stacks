module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.BaseChange

/-!
# Families of cycles on fibres

Compatibility specializations of the canonical fibre-cycle carriers to
nonnegative dimensions.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The group of `r`-cycles on the scheme-theoretic fibre of `f` at `s`. -/
abbrev fiberCycleGroup {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (s : S) (r : ℕ) : Type u :=
  CycleGroup (f.fiber s) (f.fiberRelativeDimensionFunction s) r

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry

/-- The additive group of families of `r`-cycles on fibres of `f : X ⟶ S`. -/
abbrev familyOfCyclesOnFibres {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ) : Type u :=
  f.FiberCycleFamily r

end AlgebraicGeometry
