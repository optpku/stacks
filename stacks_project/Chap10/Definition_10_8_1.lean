module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Category.Preorder
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.8.1

@stack 00D4
-/

universe u v

namespace CategoryTheory

section

variable {I : Type u} [Preorder I]
variable {R : Type v} [Ring R]

/- Definition 10.8.1: a system of `R`-modules over a preordered set `I` is exactly a functor
`I ⥤ ModuleCat R`, i.e. the specialization of Categories, Definition 4.21.2 to the category of
`R`-modules. The primitive data are the objects `F.obj i` and transition maps
`F.map (homOfLE hij)`; the identity and composition compatibilities are derived directly from the
owner abstraction's functor laws. When `I` is a directed set, this is a directed system in the
usual sense. -/
@[stacks 00D4]
#check (I ⥤ ModuleCat R)

end

end CategoryTheory
