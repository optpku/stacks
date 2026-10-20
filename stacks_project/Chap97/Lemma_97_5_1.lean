module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreservingOnObjects.BaseChange
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

/- Lemma 97.5.1: let `p : X ⟶ Y` and `q : Z ⟶ Y` be 1-morphisms of
categories fibred in groupoids over `(Sch/S)_fppf`. If `p` is limit preserving
on objects, then so is the base change `TwoFibreProduct.fst q p : X ×_Y Z ⟶ Z`
of `p` by `q`. -/
@[stacks 06CV] #check
  (AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects.pullback_fst :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (p : X ⟶ Y) (q : Z ⟶ Y)
      [AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects p],
      AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects
        (TwoFibreProduct.fst.{u + 1, u, u + 1, u} q p))
