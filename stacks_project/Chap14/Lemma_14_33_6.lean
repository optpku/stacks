module

public import ReasLib.CategoryTheory.Endofunctor.ResolutionWhiskering.Center
public import ReasLib.CategoryTheory.Endofunctor.ComonadResolution.Construction
import StacksCheckRecall

@[expose] public section

/-!
@stack 0G5S

# Left and right identity whiskering on an endofunctor resolution

This file is the source-facing facade for Lemma 14.33.6.  Augmentation compatibility is a
generic property of the `CatCenter` action, while the concrete homotopy only needs a realization
of iterated-endofunctor data.  A canonical comonad resolution is a direct specialization.
-/

open CategoryTheory

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {Y : C ⥤ C} {d : Y ⟶ 𝟭 C} {s : Y ⟶ Y ⋙ Y}
variable {X : SimplicialObject (C ⥤ C)}
variable (hX : EndofunctorResolution.Realization d s X)
variable (f : CatCenter C)

#check (Functor.whiskerLeft X (CatCenter.whiskerRight C f))
#check (Functor.whiskerLeft X (CatCenter.whiskerLeft C f))
#check (CatCenter.augmentedApp (CatCenter.whiskerRight C f) hX.augmented)
#check (CatCenter.augmentedApp (CatCenter.whiskerLeft C f) hX.augmented)
#check (fun {n : ℕ} ↦
  EndofunctorResolution.Realization.whisker.component hX f (n := n))
#check (EndofunctorResolution.Realization.whisker.homotopy hX f)

/- Lemma 14.33.6 (1): left whiskering by `f` is compatible with `f` through the standard
augmentation. -/
@[stacks 0G5S "Lemma 14.33.6 (1)"]
#check (CatCenter.whiskerRight.commSq f hX.augmentation :
  CommSq (Functor.whiskerLeft X (CatCenter.whiskerRight C f))
    hX.augmentation hX.augmentation
    ((SimplicialObject.const (C ⥤ C)).map f))

/- Lemma 14.33.6 (2): right whiskering by `f` is compatible with `f` through the standard
augmentation. -/
@[stacks 0G5S "Lemma 14.33.6 (2)"]
#check (CatCenter.whiskerLeft.commSq f hX.augmentation :
  CommSq (Functor.whiskerLeft X (CatCenter.whiskerLeft C f))
    hX.augmentation hX.augmentation
    ((SimplicialObject.const (C ⥤ C)).map f))

/- Lemma 14.33.6 (3): the two compatible simplicial endomorphisms are homotopic. -/
@[stacks 0G5S "Lemma 14.33.6 (3)"]
#check (EndofunctorResolution.Realization.whisker.homotopic hX f :
  SimplicialObject.Homotopic
    (Functor.whiskerLeft X (CatCenter.whiskerRight C f))
    (Functor.whiskerLeft X (CatCenter.whiskerLeft C f)))

section Comonad

variable (K : Comonad C)

#check (EndofunctorResolution.Realization.whisker.homotopy
  (Comonad.simplicialResolution.realization K) f)
#check (EndofunctorResolution.Realization.whisker.homotopic
  (Comonad.simplicialResolution.realization K) f :
  SimplicialObject.Homotopic
    (Functor.whiskerLeft K.simplicialResolution (CatCenter.whiskerRight C f))
    (Functor.whiskerLeft K.simplicialResolution (CatCenter.whiskerLeft C f)))

end Comonad

end CategoryTheory
