module

public import stacks_project.Chap96.Proposition_96_14_3_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Forward functor from quotient-stack QCoh to groupoid QCoh

A quasi-coherent module `F` on `[U / R]` restricts along the atlas to
`G = x^* F|_{U_étale}`, equipped with the equivariance map `α` of the atlas
2-cell. This is the functor `QCoh(𝒪_[U/R]) ⥤ QCoh(U, R, s, t, c)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.GroupoidAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)

/-- The functor sending a quasi-coherent module on `[U / R]` to the equivariant
module `(x^* F|_{U_étale}, α)` on the groupoid `(U, R, s, t, c)`. -/
def toGroupoid : QCoh G.quotientStack ⥤ G.QCoh where
  obj F :=
    GroupoidAlgebraicSpace.QCoh.of (atlasRestrict G F) (action G F)
      (action_cocycle G F) (action_unit G F)
  map {F F'} f :=
    System.Hom.of
      ((restrict (idSpace G.U.left)).map ((pullback G.atlas).map f)) sorry
  map_id := sorry
  map_comp := sorry

/-- The underlying quasi-coherent module of `toGroupoid F` is `x^* F` restricted
to the small étale site of `U`. -/
theorem toGroupoid_obj (F : QCoh G.quotientStack) :
    GroupoidAlgebraicSpace.QCoh.obj ((toGroupoid G).obj F) = atlasRestrict G F :=
  rfl

/-- The equivariance map of `toGroupoid F` is the atlas 2-cell action `α`. -/
theorem toGroupoid_action (F : QCoh G.quotientStack) :
    GroupoidAlgebraicSpace.QCoh.action ((toGroupoid G).obj F) = action G F :=
  rfl

end AlgebraicGeometry.GroupoidsOver.QCoh
