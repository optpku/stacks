module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.AbelianPushforward

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]

section

variable (f : X ⟶ Y) [Smooth f]

#check (AlgebraicGeometry.AlgebraicStack.lisseEtalePushforward f :
  Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
    Sheaf (lisseEtaleTopology Y) AddCommGrpCat.{u + 1})

variable [HasSheafify (lisseEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (lisseEtaleTopology Y) AddCommGrpCat.{u + 1}]
variable [HasInjectiveResolutions (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1})]
variable (H : Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1}) (p : ℕ)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleHigherDirectImage f H p :
  Sheaf (lisseEtaleTopology Y) AddCommGrpCat.{u + 1})

end

section

variable (f : X ⟶ Y) [Flat f]

#check (AlgebraicGeometry.AlgebraicStack.flatFppfPushforward f :
  Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1} ⥤
    Sheaf (flatFppfTopology Y) AddCommGrpCat.{u + 1})

variable [HasSheafify (flatFppfTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (flatFppfTopology Y) AddCommGrpCat.{u + 1}]
variable [HasInjectiveResolutions (Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1})]
variable (H : Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1}) (p : ℕ)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfHigherDirectImage f H p :
  Sheaf (flatFppfTopology Y) AddCommGrpCat.{u + 1})

end

end AlgebraicGeometry.AlgebraicStack
