/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Fiber
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 29.20.7: A locally finite type morphism with finite point-set fiber over `s` has a
finite discrete scheme-theoretic fiber, and is finite-type quasi-finite at every point over `s`. -/
@[stacks 02NG] #check
  (AlgebraicGeometry.Scheme.Hom.discreteTopology_fiber_of_finite_preimage_singleton :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (s : S),
      Set.Finite (f ⁻¹' ({s} : Set S)) → DiscreteTopology (f.fiber s))

#check
  (AlgebraicGeometry.Scheme.Hom.finite_fiber_of_finite_preimage_singleton :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (s : S),
      Set.Finite (f ⁻¹' ({s} : Set S)) → Finite (f.fiber s))

#check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.QuasiFiniteAt.of_finite_preimage_singleton :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (s : S),
      Set.Finite (f ⁻¹' ({s} : Set S)) → ∀ x : X, f x = s →
        Scheme.Hom.FiniteType.QuasiFiniteAt f x)
