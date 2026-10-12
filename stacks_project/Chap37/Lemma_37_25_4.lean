/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 37.25.4: containment of the associated points of a finite-type
quasi-coherent module in an open subset of a fiber is invariant under arbitrary
scheme base change. -/
@[stacks 05KQ] #check
  (AlgebraicGeometry.Scheme.Hom.associatedPoints_fiber_subset_iff_of_isPullback :
    ∀ {X S S' X' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (g' : X' ⟶ X)
    (f' : X' ⟶ S') (sq : IsPullback g' f' f g) [LocallyOfFiniteType f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (U : X.Opens)
    (s' : S'),
    ((Scheme.Modules.pullback (f.fiberι (g s'))).obj ℱ).associatedPoints ⊆
        (f.fiberι (g s')) ⁻¹' (U : Set X) ↔
      ((Scheme.Modules.pullback (f'.fiberι s')).obj
          ((Scheme.Modules.pullback g').obj ℱ)).associatedPoints ⊆
        (f'.fiberι s') ⁻¹' (g' ⁻¹' (U : Set X)))
