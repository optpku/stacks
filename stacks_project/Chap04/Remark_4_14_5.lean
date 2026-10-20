module

public import Mathlib.CategoryTheory.Limits.ConeCategory
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory.Limits

universe vJ uJ vC uC

variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]
variable (F : J ⥤ C) (c : Cone F)

/- The componentwise presentations in the source are exactly the canonical `Cone` and `Cocone`
structures: naturality of their legs is the displayed compatibility condition, and their category
instances use the standard commuting-triangle morphisms. For the universal clauses,
`Cone.isLimitEquivIsTerminal` matches the source's objectwise limit statement, whereas
`hasColimit_iff_hasInitial_cocone` matches its explicit colimit-existence equivalence. The dual
existence/objectwise variants are useful canonical companions but would strengthen or duplicate
the corresponding source-facing clause, so direct recalls of these six owners give downstream
access to the standard cone API without a project-local wrapper. -/

/- Remark 4.14.5 (1): a cone on `F : J ⥤ C` is the canonical structure `Cone F`, whose point and
natural-transformation legs give the object `W`, maps `W ⟶ F.obj i`, and their compatibility. -/
@[stacks 0G2U "cone object, legs, and compatibility"]
#check (Cone F : Type (max uJ uC vC))

/- Remark 4.14.5 (2): cones on a fixed diagram form the canonical category `Cone F`. -/
@[stacks 0G2U "category of cones and commuting-triangle morphisms"]
#check (Cone.category (F := F) : Category.{vC} (Cone F))

/- Remark 4.14.5 (3): a cone is limiting exactly when it is terminal in the category of cones. -/
@[stacks 0G2U "limit cones as terminal objects in the cone category"]
#check (Cone.isLimitEquivIsTerminal c : IsLimit c ≃ IsTerminal c)

/- Remark 4.14.5 (4): a cocone on `F : J ⥤ C` is the canonical structure `Cocone F`, whose point
and natural-transformation legs give the object `W`, maps `F.obj i ⟶ W`, and their compatibility. -/
@[stacks 0G2U "cocone object, legs, and compatibility"]
#check (Cocone F : Type (max uJ uC vC))

/- Remark 4.14.5 (5): cocones on a fixed diagram form the canonical category `Cocone F`. -/
@[stacks 0G2U "category of cocones and commuting-triangle morphisms"]
#check (Cocone.category (F := F) : Category.{vC} (Cocone F))

/- Remark 4.14.5 (6): a colimit of `F` exists exactly when the category `Cocone F` has an initial
object. -/
@[stacks 0G2U "colimit existence via an initial object in the cocone category"]
#check (hasColimit_iff_hasInitial_cocone F : HasColimit F ↔ HasInitial (Cocone F))

end CategoryTheory.Limits
