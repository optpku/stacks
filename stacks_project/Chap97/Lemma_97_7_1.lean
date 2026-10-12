/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap97.Lemma_97_7_1_SurjectiveOnObjects
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

/- Lemma 97.7.1: let `p : X ⟶ Y` and `q : Z ⟶ Y` be 1-morphisms of
categories fibred in groupoids over `(Sch/S)_fppf`. If `p` is surjective on
objects, then so is the base change `p' : X ×_Y Z ⟶ Z` of `p` by `q`. -/
@[stacks 06D5] #check
  (AlgebraicGeometry.Groupoids.Hom.SurjectiveOnObjects.pullback_fst :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Z ⟶ Y)
      [AlgebraicGeometry.Groupoids.Hom.SurjectiveOnObjects f],
      AlgebraicGeometry.Groupoids.Hom.SurjectiveOnObjects
        (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f))
