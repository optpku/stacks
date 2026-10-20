/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pro.HomColimit
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

open Limits
open scoped CategoryTheory

universe uC vC uI vI uJ vJ

variable {C : Type uC} [Category.{vC} C]
variable {I : Type uI} [Category.{vI} I] [Small.{vC} I]
variable [LocallySmall.{vC} I] [IsCofiltered I]
variable {J : Type uJ} [Category.{vJ} J] [Small.{vC} J]
variable [LocallySmall.{vC} J] [IsCofiltered J]
variable (F : I ⥤ C) (G : J ⥤ C)
variable (eta : Pro.homColimit G ⟶ Pro.homColimit F) (j : J)

/- Remark 4.22.7 (1): pro-morphisms are transformations between the corresponding Hom-colimit
functors. -/
@[stacks 0G2X "pro-object morphisms as transformations of Hom-colimit functors"]
#check (Pro.homColimit.homEquiv F G :
  ((Pro.lim I).obj F ⟶ (Pro.lim J).obj G) ≃
    (Pro.homColimit G ⟶ Pro.homColimit F))

/- Remark 4.22.7 (2): these transformations are compatible limit-colimit families. -/
@[stacks 0G2X "transformations as compatible Hom-colimit families"]
#check (Pro.homColimit.natTransEquivLimit F G :
  (Pro.homColimit G ⟶ Pro.homColimit F) ≃
    limit (G ⋙ Pro.homColimit F))

/- Remark 4.22.7 (3): the comparison evaluates a transformation on identity classes. -/
@[stacks 0G2X "evaluation on identity classes"]
#check (Pro.homColimit.natTransEquivLimit_π_apply F G eta j :
  limit.π (G ⋙ Pro.homColimit F) j
      (Pro.homColimit.natTransEquivLimit F G eta) =
    eta.app (G.obj j)
      ((colimit.ι (G.op ⋙ coyoneda) (Opposite.op j)).app
        (G.obj j) (𝟙 (G.obj j))))

end CategoryTheory
