/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient.Kernel

/-!
# Kernel of the Differential Graded Derived Localization

This leaf specializes the generic Verdier-quotient kernel API to differential graded modules.
It exposes both the object-property equality and its objectwise vanishing form.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedModule.Derived

variable {R : Type u} [CommRing R]

/-- Lemma 22.22.1 (09KW): the kernel of the homotopy-to-derived localization is exactly the
acyclic object property. -/
@[stacks 09KW "kernel of the DG derived localization"]
theorem Q_kernel_eq_acyclic (A : CochainDGAlgebra R) :
    Functor.kernel (Q.{u, v} A) = Homotopy.acyclic A := sorry

/-- A DG homotopy object becomes zero in the derived category exactly when it is acyclic. -/
@[stacks 09KW "vanishing under the DG derived localization"]
theorem Q_obj_isZero_iff (A : CochainDGAlgebra R)
    (X : K R (DifferentialGradedModule.{u, v} A)) :
    IsZero ((Q A).obj X) ↔ Homotopy.acyclic A X := sorry

end DifferentialGradedModule.Derived
