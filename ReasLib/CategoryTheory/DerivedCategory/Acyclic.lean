module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.HomotopyCategory.Acyclic.Retract
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient.Kernel

@[expose] public section

/-!
# Acyclic Objects in a Derived Localization

This leaf records the objectwise kernel of the standard homotopy-to-derived localization.  The
retract stability of the acyclic subcategory comes from the generic homological-kernel API.
-/

open CategoryTheory ComplexShape

universe w v u

namespace DerivedCategory

variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- The kernel of the homotopy-to-derived localization consists exactly of the acyclic
complexes. -/
@[stacks 05RT "acyclic objects as the kernel of derived localization"]
theorem Qh_kernel_eq_subcategoryAcyclic :
    Functor.kernel
        (Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A) =
      HomotopyCategory.subcategoryAcyclic A := sorry

end DerivedCategory
