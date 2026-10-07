module

public import ReasLib.Algebra.Module.Submodule.Filtration
public import ReasLib.CategoryTheory.Filtration.Morphism.PageRepresentatives
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u uR uM

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X Y : FilteredObject C}
variable [CompleteLattice (Subobject Y.obj)]
variable (f : X ⟶ Y) (p : ℤ)

/- Equation 12.23.5.2 [012F]: eventual boundary representatives are contained in the intrinsic
image representative.  The canonical statement applies in every abelian category. -/
@[stacks 012F]
#check (FilteredObject.Hom.Representative.Boundary.eventual_le_image f p :
  FilteredObject.Hom.eventualBoundaryRepresentative f p ≤
    FilteredObject.Hom.imageRepresentative f p)

section Module

variable {R : Type uR} [Semiring R]
variable {M : Type uM} [AddCommMonoid M] [Module R M]
variable (d : M →ₗ[R] M) (F : ℤ → Submodule R M)

/- For module calculations, the same inequality is available directly in the submodule lattice. -/
#check (Submodule.FilteredLinearMap.Representative.Boundary.eventual_le_range
  d F F p :
    Submodule.FilteredLinearMap.eventualBoundaryRepresentative d F F p ≤
      Submodule.FilteredLinearMap.rangeRepresentative d F p)

end Module
