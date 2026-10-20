/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Product
public import stacks_project.Chap65.Definition_65_6_3_Hom

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (F G : AlgebraicSpace S)

#check (AlgebraicSpace.product F G : AlgebraicSpace S)
#check (AlgebraicSpace.product_functorOfPoints F G :
  (AlgebraicSpace.product F G).functorOfPoints =
    (F.functorOfPoints ⨯ G.functorOfPoints))
#check (AlgebraicSpace.productFst F G : AlgebraicSpace.product F G ⟶ F)
#check (AlgebraicSpace.productSnd F G : AlgebraicSpace.product F G ⟶ G)
#check (AlgebraicSpace.product_isLimit F G :
  IsLimit (BinaryFan.mk (AlgebraicSpace.productFst F G) (AlgebraicSpace.productSnd F G)))

end AlgebraicGeometry.AlgebraicSpace
