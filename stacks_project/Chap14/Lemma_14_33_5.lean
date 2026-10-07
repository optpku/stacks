module

public import ReasLib.CategoryTheory.Endofunctor.ResolutionWhiskering.Interchange
public import ReasLib.CategoryTheory.Endofunctor.ComonadResolution.Augmentation
import StacksCheckRecall

@[expose] public section

/-!
@stack 0G5R

# Interchange homotopy for an iterated-endofunctor resolution

This file is the source-facing facade for Lemma 14.33.5.  The two horizontal composites and
their degreewise homotopy are owned at the general realization level by `ReasLib`; a canonical
comonad resolution is obtained by direct specialization.
-/

open CategoryTheory
open CategoryTheory.SimplicialObject

universe uA uB uC vA vB vC

namespace CategoryTheory

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
variable {Y : C ⥤ C} {d : Y ⟶ 𝟭 C} {s : Y ⟶ Y ⋙ Y}
variable {X : SimplicialObject (C ⥤ C)}

section Realization

variable (hX : EndofunctorResolution.Realization d s X)
variable {F F' : A ⥤ C} {G G' : C ⥤ B}
variable
  (α : SimplicialObject.Augmented.postcompose G hX.augmentation ⟶
    SimplicialObject.Augmented.postcompose G' hX.augmentation)
  (β : SimplicialObject.Augmented.precompose F hX.augmentation ⟶
    SimplicialObject.Augmented.precompose F' hX.augmentation)

#check (SimplicialObject.Augmented.whisker.interchange.leftRight α β)
#check (SimplicialObject.Augmented.whisker.interchange.rightLeft α β)
#check (EndofunctorResolution.Realization.interchange.splitIso hX F G)
#check (fun {n : ℕ} ↦
  EndofunctorResolution.Realization.interchange.component hX α β (n := n))
#check (EndofunctorResolution.Realization.interchange.homotopy hX α β)

/- Lemma 14.33.5: the horizontal composites `α.left ⋆ β.right` and
`α.right ⋆ β.left` are simplicially homotopic for every realization of the
iterated-endofunctor resolution data. -/
@[stacks 0G5R "Lemma 14.33.5"]
#check (EndofunctorResolution.Realization.interchange.homotopic hX α β :
  Homotopic
    (SimplicialObject.Augmented.whisker.interchange.leftRight α β).left
    (SimplicialObject.Augmented.whisker.interchange.rightLeft α β).left)

end Realization

section Comonad

variable (K : Comonad C) {F F' : A ⥤ C} {G G' : C ⥤ B}
variable
  (α : SimplicialObject.Augmented.postcompose G
      (Comonad.simplicialResolution.augmentation K) ⟶
    SimplicialObject.Augmented.postcompose G'
      (Comonad.simplicialResolution.augmentation K))
  (β : SimplicialObject.Augmented.precompose F
      (Comonad.simplicialResolution.augmentation K) ⟶
    SimplicialObject.Augmented.precompose F'
      (Comonad.simplicialResolution.augmentation K))

#check (EndofunctorResolution.Realization.interchange.homotopy
  (Comonad.simplicialResolution.realization K) α β)
#check (EndofunctorResolution.Realization.interchange.homotopic
  (Comonad.simplicialResolution.realization K) α β :
  Homotopic
    (SimplicialObject.Augmented.whisker.interchange.leftRight α β).left
    (SimplicialObject.Augmented.whisker.interchange.rightLeft α β).left)

end Comonad

end CategoryTheory
