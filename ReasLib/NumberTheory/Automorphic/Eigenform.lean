/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.ClosedPoints

/-! Hecke eigenvalue systems attached to unramified forms. -/

@[expose] public section
open AlgebraicGeometry TopologicalSpace
universe u v
namespace AlgebraicGeometry.SchemeOverField
variable {k : Type u} [Field k]
variable {Λ : Type v} [CommRing Λ]

/-- An eigenform records the eigenvalue families for the two Hecke operators. -/
structure Eigenform (X : SchemeOverField k) (Λ : Type v) [CommRing Λ] where
  /-- The eigenvalues of the `T` operators at closed points. -/
  t : closedPoints X.left → Λ
  /-- The eigenvalues of the `U` operators at closed points. -/
  u : closedPoints X.left → Λˣ

namespace Eigenform
variable (X : SchemeOverField k)

/-- Construct an eigenvalue system from its `T` and `U` eigenvalue families. -/
def of (t : closedPoints X.left → Λ) (u : closedPoints X.left → Λˣ) : Eigenform X Λ :=
  { t := t, u := u }

/-- The `T` eigenvalue family of an explicitly constructed eigenvalue system. -/
theorem t_apply (t : closedPoints X.left → Λ) (u : closedPoints X.left → Λˣ) :
    (of X t u).t = t := rfl

/-- The `U` eigenvalue family of an explicitly constructed eigenvalue system. -/
theorem u_apply (t : closedPoints X.left → Λ) (u : closedPoints X.left → Λˣ) :
    (of X t u).u = u := rfl

/-- Every eigenvalue system is reconstructed from its two component families. -/
theorem spec (f : Eigenform X Λ) : f = of X f.t f.u := by cases f; rfl

end Eigenform
end AlgebraicGeometry.SchemeOverField
