/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative.GenericPoints
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

/- Lemma 37.25.1: a relatively associated point has a nonempty open subscheme of its
reduced closure whose fiberwise generic points remain in the relative assassin. -/
@[stacks 05F1] #check
  (AlgebraicGeometry.Scheme.Modules.relativeAssassin.exists_open_pointClosure_fiber_genericPoints :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    {ξ : X} (_ : ξ ∈ relativeAssassin f ℱ),
      ∃ V : (PointClosure.scheme ξ).Opens, Nonempty V ∧
        ∀ s : S, s ∈ Set.range (V.ι ≫ PointClosure.ι ξ ≫ f).base →
          Set.MapsTo
            ((V.ι ≫ PointClosure.ι ξ ≫ f).fiberι s ≫ V.ι ≫ PointClosure.ι ξ).base
            (genericPoints ((V.ι ≫ PointClosure.ι ξ ≫ f).fiber s))
            (relativeAssassin f ℱ))
