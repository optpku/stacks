/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# The finite-type quasi-finite locus

This file defines the open locus where a scheme morphism is both of finite type and
quasi-finite at a point, together with the local properties of the induced morphism.
The resulting open is characterized pointwise by the corresponding quasi-finiteness predicate.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The set of points where a scheme morphism is finite type and quasi-finite at the point is
open. -/
theorem FiniteType.isOpen_quasiFiniteAt :
    IsOpen {x : X | FiniteType.QuasiFiniteAt f x} := sorry

/-- The open locus where a scheme morphism is finite type and quasi-finite at the point. -/
def FiniteType.quasiFiniteLocus : X.Opens :=
  ⟨{x : X | FiniteType.QuasiFiniteAt f x}, FiniteType.isOpen_quasiFiniteAt f⟩

/-- A point lies in the finite-type quasi-finite locus exactly when the morphism is finite type
and quasi-finite there. -/
theorem FiniteType.mem_quasiFiniteLocus (x : X) :
    x ∈ FiniteType.quasiFiniteLocus f ↔ FiniteType.QuasiFiniteAt f x := sorry

/-- The morphism induced on the finite-type quasi-finite locus is locally of finite type and
locally quasi-finite. -/
theorem FiniteType.locallyQuasiFinite_quasiFiniteLocus :
    LocallyOfFiniteType ((FiniteType.quasiFiniteLocus f).ι ≫ f) ∧
      LocallyQuasiFinite ((FiniteType.quasiFiniteLocus f).ι ≫ f) := sorry

end Scheme.Hom
end AlgebraicGeometry
