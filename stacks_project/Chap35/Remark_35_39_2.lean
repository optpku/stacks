module

public import ReasLib.CategoryTheory.Sites.Descent.Representable.Restriction
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

/- Remark 35.39.2: representability after multiplication by each family member is
equivalent to representability after restriction to the corresponding slice site. -/
@[stacks 02W6] #check
  (CategoryTheory.GrothendieckTopology.RepresentableDescent.locallyRepresentableAlong_iff_restrictionsRepresentable :
    ∀ {C : Type u} [Category.{v} C] [HasPullbacks C]
      (J : GrothendieckTopology C) [J.Subcanonical] {S : C}
      {I : Type (max u v)} {Y : I → C} (p : ∀ i, Y i ⟶ S)
      (F : Sheaf (J.over S) (Type (max u v))),
      CategoryTheory.GrothendieckTopology.RepresentableDescent.locallyRepresentableAlong J p F ↔
        ∀ i, ((J.over (Y i)).uliftYoneda.{max u v}).essImage
          ((J.overMapPullback (Type (max u v)) (p i)).obj F))
