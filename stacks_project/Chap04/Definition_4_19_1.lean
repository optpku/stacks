module

public import ReasLib.CategoryTheory.Filtered.ModuloKernel.Transport
import StacksCheckRecall

@[expose] public section

universe vI uI vC uC

namespace CategoryTheory

variable {I : Type uI} [Category.{vI} I]
variable {C : Type uC} [Category.{vC} C]
variable (M : I ⥤ C)

/- Definition 4.19.1 (1): a diagram is filtered modulo its kernel when the quotient of its index
category by equality after applying the diagram is filtered. -/
@[stacks 002V "filtered diagrams via common successors and image equalizers"]
#check (M.IsFilteredModuloKernel : Prop)

/- Definition 4.19.1 (2): the elementary source conditions and the faithful-specialization
criterion are exposed by the neutral support API. -/
@[stacks 002V "filtered index categories via the identity diagram"]
#check (Functor.IsFilteredModuloKernel.iff_of_faithful (𝟭 I) :
  (𝟭 I).IsFilteredModuloKernel ↔ IsFiltered I)

end CategoryTheory
