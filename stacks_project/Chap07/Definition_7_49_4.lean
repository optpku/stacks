module

public import ReasLib.CategoryTheory.Sites.TypeSheafification
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite GrothendieckTopology

universe u v

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (F : Cᵒᵖ ⥤ Type (max u v))

/- Definition 7.49.4 (1): the sheaf associated to a set-valued presheaf F is F^# := LL F,
realized as the iterated plus object J.plusObj (J.plusObj F). -/
@[stacks 00ZL "associated sheaf as double plus"]
#check (J.plusObj (J.plusObj F) : Cᵒᵖ ⥤ Type (max u v))

/- Definition 7.49.4 (2): the canonical map F ⟶ F^# is the composite of the two plus units. -/
@[stacks 00ZL "double-plus canonical map"]
#check (J.toPlus F ≫ J.toPlus (J.plusObj F))
