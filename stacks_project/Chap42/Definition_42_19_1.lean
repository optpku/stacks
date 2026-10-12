/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ChowGroup
import stacks_project.Chap42.Situation_42_7_1
import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction

open AlgebraicGeometry

universe u v

section

variable {S X : Scheme.{u}} (p : X ⟶ S)
variable [UniversallyCatenary S] [LocallyOfFiniteType p]
variable (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)

/- Definition 42.19.1 (1): A locally finite family of rational functions on integral closed
subschemes of relative dimension `k + 1` determines a rational boundary in `Z_k(X)`. -/
@[stacks 02RW] #check
  (@AlgebraicGeometry.RationalEquivalence.boundary X
    (LocallyOfFiniteType.isLocallyNoetherian p) (p.relativeDimensionFunction δ)
    inferInstance k :
      {J : Type v} →
        (x : J → X) →
        (hx : ∀ j, p.relativeDimensionFunction δ (x j) = k + 1) →
        (f : ∀ j,
          (AlgebraicGeometry.Scheme.PointClosure.scheme (x j)).functionFieldˣ) →
        (hlocal : LocallyFinite fun j ↦
          (AlgebraicGeometry.Scheme.PointClosure.closedSubset (x j) : Set X)) →
        AlgebraicGeometry.CycleGroup X (p.relativeDimensionFunction δ) k)

/- Definition 42.19.1 (2): A degree-`k` cycle is rationally equivalent to zero precisely when it
is such a locally finite boundary. -/
@[stacks 02RW] #check
  (@AlgebraicGeometry.RationalEquivalence.IsRationallyTrivial X
    (LocallyOfFiniteType.isLocallyNoetherian p) (p.relativeDimensionFunction δ)
    inferInstance k :
      AlgebraicGeometry.CycleGroup X (p.relativeDimensionFunction δ) k → Prop)

/- Definition 42.19.1 (3): Two degree-`k` cycles are rationally equivalent when their difference
is rationally equivalent to zero. -/
@[stacks 02RW] #check
  (@AlgebraicGeometry.RationalEquivalence.RationallyEquivalent X
    (LocallyOfFiniteType.isLocallyNoetherian p) (p.relativeDimensionFunction δ)
    inferInstance k :
      AlgebraicGeometry.CycleGroup X (p.relativeDimensionFunction δ) k →
        AlgebraicGeometry.CycleGroup X (p.relativeDimensionFunction δ) k → Prop)

/- Definition 42.19.1 (4): `CH_k(X)` is the quotient of `Z_k(X)` by rational equivalence. -/
@[stacks 02RW] #check
  (@AlgebraicGeometry.ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
    (p.relativeDimensionFunction δ) inferInstance k : Type u)

end
