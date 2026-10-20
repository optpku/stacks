module

public import ReasLib.AlgebraicTopology.SimplicialObject.Augmentation
import StacksCheckRecall

/-!
@stack 018H

# Lemma 14.20.2 compatibility facade

The generic classification of augmentations by a compatible zero-simplex is owned by
`ReasLib.AlgebraicTopology.SimplicialObject.Augmentation`. This module retains the historical
Chapter 14 import path and source traceability.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial

universe u v

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]
variable (U : SimplicialObject C) (X : C)
variable (alpha : U ⟶ (const C).obj X) (e : Augmentation.Compatible U X)
variable {V : SimplicialObject C} {Y : C} (f : V ⟶ U) (g : X ⟶ Y)

/- Lemma 14.20.2: augmentations are classified by compatible degree-zero maps. -/
@[stacks 018H]
#check (Augmentation.equiv U X :
  (U ⟶ (const C).obj X) ≃ Augmentation.Compatible U X)

/- Companion computation: the forward classifier is evaluation in degree zero. -/
#check (Augmentation.equiv.apply U X alpha :
  Augmentation.equiv U X alpha =
    ⟨alpha.app (op ⦋0⦌), Augmentation.face_eq alpha⟩)

/- Companion computation: reconstruction has the prescribed degree-zero component. -/
#check (Augmentation.equiv.symm_apply_app_zero U X e :
  ((Augmentation.equiv U X).symm e).app (op ⦋0⦌) = e.1)

#check (e.precomp f)
#check (e.postcomp g)
#check (Augmentation.equiv.precomp f alpha)
#check (Augmentation.equiv.postcomp alpha g)
#check @Augmentation.hom_ext

end CategoryTheory.SimplicialObject
