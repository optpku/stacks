module

import ReasLib.CategoryTheory.DerivedCategory.Acyclic
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open ComplexShape

universe w v u

variable (A : Type u) [Category.{v} A] [Abelian A]

/- Lemma 13.11.2: the acyclic complexes form a strictly full, retract-stable triangulated
subcategory of the homotopy category. -/
@[stacks 05RT] #check (inferInstance :
  (HomotopyCategory.subcategoryAcyclic A).IsStableUnderRetracts)

@[stacks 05RT] #check (inferInstance :
  (HomotopyCategory.subcategoryAcyclic A).IsClosedUnderIsomorphisms)

@[stacks 05RT] #check (inferInstance :
  (HomotopyCategory.subcategoryAcyclic A).IsTriangulated)

/- The corresponding cone-defined system is the canonical quasi-isomorphism property. -/
@[stacks 05RT] #check (HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic A)

section

variable [HasDerivedCategory.{w} A]

/- The kernel of the chosen homotopy-to-derived localization is the acyclic subcategory. -/
@[stacks 05RT] #check (DerivedCategory.Qh_kernel_eq_subcategoryAcyclic A)

/- Degree-zero homology factors through the chosen localization. -/
@[stacks 05RT] #check (DerivedCategory.homologyFunctorFactorsh A 0)

end
