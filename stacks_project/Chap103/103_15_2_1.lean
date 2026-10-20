module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.HigherDirectImage
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]

section

variable [HasSheafify (lisseEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (lisseEtaleTopology Y) AddCommGrpCat.{u + 1}]
variable [HasInjectiveResolutions (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1})]
variable (f : X ⟶ Y) [Smooth f]
variable (H : Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1}) (p : ℕ)

/- 103.15.2.1 (1): Higher direct image is the sheaf associated to
primed-site cohomology of the pullback of H. -/
@[stacks 07AW] #check
  (AlgebraicGeometry.AlgebraicStack.lisseEtaleHigherDirectImageIso f H p :
    lisseEtaleHigherDirectImage f H p ≅
      (presheafToSheaf (lisseEtaleTopology Y) AddCommGrpCat.{u + 1}).obj
        (lisseEtaleHigherDirectImagePresheaf f H p))

end

section

variable [HasSheafify (flatFppfTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (flatFppfTopology Y) AddCommGrpCat.{u + 1}]
variable [HasInjectiveResolutions (Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1})]
variable (f : X ⟶ Y) [Flat f]
variable (H : Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1}) (p : ℕ)

/- 103.15.2.1 (2): Higher direct image is the sheaf associated to
primed-site cohomology of the pullback of H. -/
@[stacks 07AW] #check
  (AlgebraicGeometry.AlgebraicStack.flatFppfHigherDirectImageIso f H p :
    flatFppfHigherDirectImage f H p ≅
      (presheafToSheaf (flatFppfTopology Y) AddCommGrpCat.{u + 1}).obj
        (flatFppfHigherDirectImagePresheaf f H p))

end

end AlgebraicGeometry.AlgebraicStack
