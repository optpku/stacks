/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.BaseChange
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 29.36.17 (1): in a cartesian square of schemes, the étale locus of the base-changed
morphism is the inverse image of the original étale locus when the original morphism is flat and
locally of finite presentation. -/
@[stacks 0476] #check
  (AlgebraicGeometry.Scheme.Hom.etaleAt_open_eq_preimage_of_isPullback_of_flat :
    ∀ {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
      (f : X ⟶ S) (g : S' ⟶ S) (hcart : IsPullback g' f' f g)
      [Flat f] [LocallyOfFinitePresentation f] (W : X.Opens) (W' : X'.Opens)
      (hW : (W : Set X) = {x : X | f.EtaleAt x})
      (hW' : (W' : Set X') = {x' : X' | f'.EtaleAt x'}),
      W' = g' ⁻¹ᵁ W)

/- In the second case, the original morphism is locally of finite presentation and the base
morphism is flat. -/
#check
  (AlgebraicGeometry.Scheme.Hom.etaleAt_open_eq_preimage_of_isPullback_of_flat_base :
    ∀ {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
      (f : X ⟶ S) (g : S' ⟶ S) (hcart : IsPullback g' f' f g)
      [LocallyOfFinitePresentation f] [Flat g] (W : X.Opens) (W' : X'.Opens)
      (hW : (W : Set X) = {x : X | f.EtaleAt x})
      (hW' : (W' : Set X') = {x' : X' | f'.EtaleAt x'}),
      W' = g' ⁻¹ᵁ W)
