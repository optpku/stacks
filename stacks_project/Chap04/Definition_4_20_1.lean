module

public import ReasLib.CategoryTheory.Filtered.ModuloKernel.Transport
import StacksCheckRecall

@[expose] public section

universe vI uI vC uC

namespace CategoryTheory

variable {I : Type uI} [Category.{vI} I]
variable {C : Type uC} [Category.{vC} C]
variable (M : I ⥤ C)

/- Definition 4.20.1 (1): a diagram is cofiltered modulo its kernel when its opposite diagram is
filtered modulo its kernel. -/
@[stacks 04AZ "cofiltered diagrams"]
#check (M.IsCofilteredModuloKernel : Prop)

/- Definition 4.20.1 (2): the elementary dual conditions and faithful-specialization criterion
are exposed by the neutral support API. -/
@[stacks 04AZ "cofiltered index categories via identity diagrams"]
#check (Functor.IsCofilteredModuloKernel.iff_of_faithful (𝟭 I) :
  (𝟭 I).IsCofilteredModuloKernel ↔ IsCofiltered I)

end CategoryTheory
