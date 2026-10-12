/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative.BaseChange.Algebraic

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Remark 31.7.4 (1): with notation and assumptions as in Lemma 31.7.3, the inverse image of
the relative assassin on `X` contains the relative assassin after base change. -/
@[stacks 05KL] #check
  (AlgebraicGeometry.Scheme.Modules.relativeAssassin.pullback_subset_preimage :
    ∀ {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X}
      {f' : X' ⟶ S'} (sq : IsPullback g' f' f g) [LocallyOfFiniteType f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      AlgebraicGeometry.Scheme.Modules.relativeAssassin f'
          ((AlgebraicGeometry.Scheme.Modules.pullback g').obj ℱ) ⊆
        g' ⁻¹' AlgebraicGeometry.Scheme.Modules.relativeAssassin f ℱ)

/- Remark 31.7.4 (2): if `g : S' ⟶ S` is locally quasi-finite, then the inverse image of
the relative assassin equals the relative assassin after base change. -/
@[stacks 05KL] #check
  (AlgebraicGeometry.Scheme.Modules.relativeAssassin.preimage_eq_pullback_of_locallyQuasiFinite :
    ∀ {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X}
      {f' : X' ⟶ S'} (sq : IsPullback g' f' f g) [LocallyOfFiniteType f]
      [LocallyQuasiFinite g] (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      g' ⁻¹' AlgebraicGeometry.Scheme.Modules.relativeAssassin f ℱ =
        AlgebraicGeometry.Scheme.Modules.relativeAssassin f'
          ((AlgebraicGeometry.Scheme.Modules.pullback g').obj ℱ))

/- Remark 31.7.4 (3): the same equality holds whenever every residue-field extension
`κ(g(s')) → κ(s')` induced by `g : S' ⟶ S` is algebraic. -/
@[stacks 05KL] #check
  (AlgebraicGeometry.Scheme.Modules.relativeAssassin.preimage_eq_pullback_of_algebraicResidueFieldExtensions :
    ∀ {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X}
      {f' : X' ⟶ S'} (sq : IsPullback g' f' f g) [LocallyOfFiniteType f]
      (hg : AlgebraicGeometry.Scheme.Hom.HasAlgebraicResidueFieldExtensions g)
      (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      g' ⁻¹' AlgebraicGeometry.Scheme.Modules.relativeAssassin f ℱ =
        AlgebraicGeometry.Scheme.Modules.relativeAssassin f'
          ((AlgebraicGeometry.Scheme.Modules.pullback g').obj ℱ))
