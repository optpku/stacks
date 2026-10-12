/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalRing.ResidueField.Cotangent.JacobiZariski.Row
public import ReasLib.RingTheory.Smooth.Adic.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Adic formal smoothness and the residue-field Jacobi--Zariski row

@stack 0DYH

This leaf adds the topological hypothesis used to make the first nonzero arrow
of the residue-field Jacobi--Zariski row injective.  All algebraic maps and
exactness criteria remain in the lower leaves.
-/

@[expose] public section

open Algebra
open IsLocalRing

universe u v

namespace Algebra.H1Cotangent.ResidueField

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
variable [IsNoetherianRing A] [IsNoetherianRing B]

/-- Adic formal smoothness makes the first nonzero residue-field
Jacobi--Zariski arrow injective. -/
@[stacks 0DYH "formal-smooth residue H₁ injectivity"]
theorem injective_of_formallySmoothAdic
    (hfs : RingHom.formally_smooth_for_adic (algebraMap A B) (maximalIdeal B)) :
    Function.Injective (toCotangent A B) := sorry

end

section

variable {A B : Type u}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
variable [IsNoetherianRing A] [IsNoetherianRing B]

/-- Adic formal smoothness makes the complete residue-field
Jacobi--Zariski row exact.  This theorem uses the same-universe `ModuleCat`
facade; the injectivity companion above is universe-polymorphic. -/
@[stacks 0DYH "formal-smooth residue-field Jacobi--Zariski exact row"]
theorem row_exact_of_formallySmoothAdic
    (hfs : RingHom.formally_smooth_for_adic (algebraMap A B) (maximalIdeal B)) :
    (row A B).Exact := sorry

end

end Algebra.H1Cotangent.ResidueField
