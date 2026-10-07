module

public import stacks_project.Chap90.Definition_90_25_1_Groupoid
public import stacks_project.Chap90.Remarks_90_5_2_Grothendieck

/-!
# The quotient category cofibered in groupoids

The quotient `[U/R]` of a groupoid in functors is the category cofibered in groupoids
associated to the functor `C ⥤ Grpd` of fibre groupoids, realized by the Grothendieck
construction.
-/

@[expose] public section

open CategoryTheory

noncomputable section
open scoped Bicategory BasedFunctor

universe u v w

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory.GroupoidInFunctors

/-- The Grothendieck projection of the fibre-groupoid functor of `G`. -/
abbrev quotientFunctor (G : GroupoidInFunctors.{u, v, w} C) :
    Grothendieck (G.toFunctor ⋙ Grpd.forgetToCat) ⥤ C :=
  Functor.groupoidCopresheafProjection G.toFunctor

/-- The Grothendieck projection of a groupoid in functors is cofibered in groupoids. -/
instance quotientFunctor_op_inGroupoids (G : GroupoidInFunctors.{u, v, w} C) :
    Functor.IsFibered.InGroupoids (quotientFunctor G).op :=
  Functor.groupoidCopresheafProjection.op_inGroupoids G.toFunctor

/-- The quotient category cofibered in groupoids `[U/R]` associated to a groupoid in
functors. -/
def quotient (G : GroupoidInFunctors.{u, v, w} C) :
    CofiberedCategoryOver.Groupoids C :=
  Functor.ofGroupoidValued G.toFunctor

/-- The projection of `[U/R]` is the Grothendieck forgetful functor of `G.toFunctor`. -/
theorem quotient_p (G : GroupoidInFunctors.{u, v, w} C) :
    (quotient G).p = quotientFunctor G := sorry

/-- The total category of `[U/R]` is the Grothendieck construction of `G.toFunctor`. -/
theorem quotient_total (G : GroupoidInFunctors.{u, v, w} C) :
    (quotient G).total = Grothendieck (G.toFunctor ⋙ Grpd.forgetToCat) := sorry

end CategoryTheory.GroupoidInFunctors

