/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.ClosedPoints

/-!
# Hecke eigenvalues of unramified GL₂ eigenforms

This leaf owns the Hecke eigenvalue package `(t_v, u_v)` of an unramified
`GL (Fin 2)` eigenform on the closed points of a curve, independently of the
adelic cusp-form carrier.
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u v

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable {Λ : Type v} [CommRing Λ]

/-- The Hecke eigenvalue system of an unramified `GL (Fin 2)` eigenform on `X`,
with values in the coefficient ring `Λ`. The family `t` records the eigenvalues
of the operators `T_v`, and the family `u` records the eigenvalues of the
operators `U_v`, as `v` runs over the closed points of `X`. -/
structure Eigenform (X : SchemeOverField k) (Λ : Type v) [CommRing Λ] where
  /-- The Hecke eigenvalues `t_v` of the operators `T_v`. -/
  t : closedPoints X.left → Λ
  /-- The Hecke eigenvalues `u_v` of the operators `U_v`. -/
  u : closedPoints X.left → Λˣ

namespace Eigenform

variable (X : SchemeOverField k)

/-- The eigenvalue system with the given families `t` and `u`. -/
def of (t : closedPoints X.left → Λ) (u : closedPoints X.left → Λˣ) :
    Eigenform X Λ where
  t := t
  u := u

/-- The `t`-family of `of X t u` is `t`. -/
theorem t_apply (t : closedPoints X.left → Λ) (u : closedPoints X.left → Λˣ) :
    (of X t u).t = t := sorry

/-- The `u`-family of `of X t u` is `u`. -/
theorem u_apply (t : closedPoints X.left → Λ) (u : closedPoints X.left → Λˣ) :
    (of X t u).u = u := sorry

/-- An eigenvalue system is recovered from its `t` and `u` families. -/
theorem spec (f : Eigenform X Λ) : f = of X f.t f.u := sorry

/-- Each `U`-eigenvalue of an eigenform is a unit in the coefficient ring. -/
theorem isUnit_u (f : Eigenform X Λ) (v : closedPoints X.left) :
    IsUnit (f.u v).val := sorry

end Eigenform

end AlgebraicGeometry.SchemeOverField
