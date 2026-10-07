module

public import ReasLib.CategoryTheory.Sites.Descent.Representable

/-!
# Representability after restriction to a slice site

This module compares representability after multiplying by a representable sheaf with
representability after restriction to the corresponding slice site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.GrothendieckTopology.RepresentableDescent

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable (J : GrothendieckTopology C) [J.Subcanonical]
variable {S X : C}

/-- Multiplication by the representable associated to `p : X ⟶ S` detects the same
representability condition as restriction from the slice over `S` to the slice over `X`. -/
theorem prodRepresentable_iff_restrictionRepresentable (p : X ⟶ S)
    (F : Sheaf (J.over S) (Type (max u v))) :
    ((J.over S).uliftYoneda.{max u v}).essImage
        (Limits.prod ((J.over S).uliftYoneda.{max u v}.obj (Over.mk p)) F) ↔
      ((J.over X).uliftYoneda.{max u v}).essImage
        ((J.overMapPullback (Type (max u v)) p).obj F) := sorry

variable {I : Type (max u v)} {Y : I → C} (p : ∀ i, Y i ⟶ S)

/-- Local representability along a family is equivalent to representability of every
restriction to the corresponding slice site. -/
theorem locallyRepresentableAlong_iff_restrictionsRepresentable
    (F : Sheaf (J.over S) (Type (max u v))) :
    locallyRepresentableAlong J p F ↔
      ∀ i, ((J.over (Y i)).uliftYoneda.{max u v}).essImage
        ((J.overMapPullback (Type (max u v)) (p i)).obj F) := sorry

end CategoryTheory.GrothendieckTopology.RepresentableDescent
