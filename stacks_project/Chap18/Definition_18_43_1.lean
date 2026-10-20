module

public import ReasLib.CategoryTheory.Sites.LocallyConstant.Basic
import StacksCheckRecall

/-!
# Definition 18.43.1 compatibility entry point

Constant sheaves use Mathlib's `Sheaf.IsConstant`; the property-parametric
locally constant owner is provided by ReasLib.
-/

@[expose] public section

open CategoryTheory

universe u v w w'

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {D : Type w} [Category.{w'} D]
variable [HasWeakSheafify J D]
variable [∀ U : C, HasWeakSheafify (J.over U) D]
variable (F : Sheaf J D)

/- Definition 18.43.1 (1): a constant sheaf is an object in the essential image of the
constant-sheaf functor. -/
@[stacks 093Q "(1)"]
#check (IsConstant J F : Prop)

/- Definition 18.43.1 (2): a locally constant sheaf locally admits constant models. -/
@[stacks 093Q "(2)"]
#check (IsLocallyConstant F : Prop)

/- The reusable property-parametric owner specializes local constant models by a predicate on
their values. -/
#check (IsLocallyConstantWith (J := J) (fun _ : D ↦ True) F : Prop)

end CategoryTheory.Sheaf
