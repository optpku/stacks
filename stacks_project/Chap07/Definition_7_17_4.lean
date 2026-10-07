module

public import ReasLib.CategoryTheory.Sites.QuasiCompact.Sheaf
import StacksCheckRecall

/-!
# Definition 7.17.4

Quasi-compactness in a sheaf topos is owned by the neutral ReasLib site layer.
-/

@[expose] public section

open CategoryTheory Limits

universe u v

/- Definition 7.17.4 (0D07) (1): quasi-compact objects of a sheaf topos. -/
@[stacks 0D07 "(1)"] #check @CategoryTheory.Sheaf.IsQuasiCompactObject

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type (max u v))]

/- Definition 7.17.4 (0D07) (2): the terminal-object specialization defining a
quasi-compact topos. -/
@[stacks 0D07 "(2)"]
#check (IsQuasiCompact J : Prop)

end CategoryTheory.GrothendieckTopology
