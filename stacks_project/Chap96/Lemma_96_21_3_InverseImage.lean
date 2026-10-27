/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.InverseImage

open AlgebraicGeometry CategoryTheory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y Y' : GroupoidsOver S}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (τ : StandardTopology)

#check (AlgebraicGeometry.GroupoidsOver.fibreProductApex f g : GroupoidsOver S)
#check (AlgebraicGeometry.GroupoidsOver.fibreProductFst f g : fibreProductApex f g ⟶ Y')
#check (AlgebraicGeometry.GroupoidsOver.fibreProductSnd f g : fibreProductApex f g ⟶ X)
#check (AlgebraicGeometry.GroupoidsOver.associatedAbelianInverseImage f τ :
  Sheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1} ⥤
    Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})

end AlgebraicGeometry.GroupoidsOver
