/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Blowup.BaseChange

open CategoryTheory

universe u

/- Lemma 31.32.3: let `f : X₁ ⟶ X₂` be a flat morphism of schemes. Let `I₂` define a
closed subscheme of `X₂`, and let `I₂.comap f` define its inverse image in `X₁`. If `bᵢ` is
the blowup in the corresponding center for `i = 1, 2`, then there is a morphism between the
blowups making the resulting square cartesian. -/
@[stacks 0805] #check
  (AlgebraicGeometry.IsBlowup.exists_isPullback_of_flat :
    ∀ {X₁ X₂ X₁' X₂' : AlgebraicGeometry.Scheme.{u}}
      (f : X₁ ⟶ X₂) (I₂ : X₂.IdealSheafData)
      (b₁ : X₁' ⟶ X₁) (b₂ : X₂' ⟶ X₂) [AlgebraicGeometry.Flat f]
      [AlgebraicGeometry.IsBlowup b₁ (I₂.comap f)] [AlgebraicGeometry.IsBlowup b₂ I₂],
      ∃ g' : X₁' ⟶ X₂', CategoryTheory.IsPullback g' b₁ b₂ f)
