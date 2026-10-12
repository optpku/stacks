/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.BaseChange

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.34.15 (1): in a cartesian square of schemes, if the original morphism is flat and
locally of finite presentation, its smooth locus pulls back to the smooth locus of the base
change. -/
@[stacks 02V4] #check
  (AlgebraicGeometry.Scheme.Hom.smoothAt_open_eq_preimage_of_isPullback_of_flat :
    ∀ {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
      (hcart : IsPullback g' f' f g) [Flat f] [LocallyOfFinitePresentation f]
      (W : X.Opens) (W' : X'.Opens)
      (hW : (W : Set X) = {x : X | f.SmoothAt x})
      (hW' : (W' : Set X') = {x' : X' | f'.SmoothAt x'}),
      W' = g' ⁻¹ᵁ W)

/- Lemma 29.34.15 (2): in a cartesian square of schemes over a flat base morphism, if the
original morphism is locally of finite presentation, its smooth locus pulls back to the smooth
locus of the base change. -/
@[stacks 02V4] #check
  (AlgebraicGeometry.Scheme.Hom.smoothAt_open_eq_preimage_of_isPullback_of_flat_base :
    ∀ {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
      (hcart : IsPullback g' f' f g) [LocallyOfFinitePresentation f] [Flat g]
      (W : X.Opens) (W' : X'.Opens)
      (hW : (W : Set X) = {x : X | f.SmoothAt x})
      (hW' : (W' : Set X') = {x' : X' | f'.SmoothAt x'}),
      W' = g' ⁻¹ᵁ W)
