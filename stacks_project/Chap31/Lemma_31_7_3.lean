/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative.BaseChange

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 31.7.3: relative associated points under an arbitrary cartesian base change are
characterized by relative association of the image and genericity in the residue-field tensor
spectrum determined by the point. -/
@[stacks 05DC] #check (
  AlgebraicGeometry.Scheme.Modules.relativeAssassin.mem_pullback_iff :
    ∀ {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X}
      {f' : X' ⟶ S'} (sq : IsPullback g' f' f g) [LocallyOfFiniteType f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] (x' : X'),
      x' ∈ Scheme.Modules.relativeAssassin f'
          ((Scheme.Modules.pullback g').obj ℱ) ↔
        g' x' ∈ Scheme.Modules.relativeAssassin f ℱ ∧
          let z : (CategoryTheory.Limits.pullback f g : Scheme) := sq.isoPullback.hom x'
          Scheme.Pullback.SpecOfPoint z ∈
            genericPoints (AlgebraicGeometry.Spec (Scheme.Pullback.Triplet.ofPoint z).tensor))
