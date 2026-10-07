module

public import stacks_project.Chap97.Lemma_97_6_1_Pullback
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

/- Lemma 97.6.1: let `p : X ⟶ Y` and `q : Z ⟶ Y` be 1-morphisms of
categories fibred in groupoids over `(Sch/S)_fppf`. If `p` is formally smooth
on objects, then so is the base change `TwoFibreProduct.fst q p : X ×_Y Z ⟶ Z`
of `p` by `q`. -/
@[stacks 06D1] #check
  (AlgebraicGeometry.Groupoids.Hom.FormallySmoothOnObjects.pullback_fst :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (p : X ⟶ Y) (q : Z ⟶ Y)
      [AlgebraicGeometry.Groupoids.Hom.FormallySmoothOnObjects p],
      AlgebraicGeometry.Groupoids.Hom.FormallySmoothOnObjects
        (TwoFibreProduct.fst.{u + 1, u, u + 1, u} q p))
