/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.ChangeOfRings
public import ReasLib.Algebra.Homology.Koszul.PowerTower
public import ReasLib.RingTheory.Ideal.Principal
import Mathlib.Tactic.CrossRefAttribute

/-!
# A change-of-rings derived tensor counterexample

For `R = k[x, y]`, `A = R/(xy)`, `N = A/(x)`, and `N' = A`, restricting the left
or right factor to `R` produces nonisomorphic objects of `D(A)`.  This leaf owns the explicit
quotient data and the two source comparison objects; the resolution calculations remain proof
obligations.

@stack 08YT
-/

@[expose] public section

noncomputable section

open CategoryTheory
open MvPolynomial Opposite
open scoped DerivedTensorChangeOfRings KoszulComplex

universe u

namespace CategoryTheory.DerivedTensorChangeOfRings.Counterexample

variable (k : Type u) [CommRing k]

/-- The polynomial base ring `k[x, y]` in the change-of-rings counterexample. -/
@[stacks 08YT "polynomial base ring"]
abbrev baseRing : Type u := MvPolynomial (Fin 2) k

/-- The target ring `A = k[x, y]/(xy)` in the change-of-rings counterexample. -/
@[stacks 08YT "nodal target ring"]
noncomputable abbrev targetRing : Type u :=
  baseRing k ⧸ principalIdeal
    ((X (0 : Fin 2) : baseRing k) * (X (1 : Fin 2) : baseRing k))

/-- The class of the first polynomial variable in `targetRing k`. -/
@[stacks 08YT "first quotient generator"]
noncomputable abbrev x : targetRing k :=
  Ideal.Quotient.mk (principalIdeal
    ((X (0 : Fin 2) : baseRing k) * (X (1 : Fin 2) : baseRing k)))
    (X (0 : Fin 2) : baseRing k)

/-- The class of the second polynomial variable in `targetRing k`. -/
@[stacks 08YT "second quotient generator"]
noncomputable abbrev y : targetRing k :=
  Ideal.Quotient.mk (principalIdeal
    ((X (0 : Fin 2) : baseRing k) * (X (1 : Fin 2) : baseRing k)))
    (X (1 : Fin 2) : baseRing k)

/-- The degree-zero object associated with `N = A/(x)`. -/
@[stacks 08YT "quotient derived object"]
noncomputable abbrev quotientObject : DerivedCategory (ModuleCat (targetRing k)) :=
  ModuleCat.single0Functor.obj
    (ModuleCat.of (targetRing k) ((targetRing k) ⧸ principalIdeal (x k)))

/-- The degree-zero object associated with the regular module `N' = A`. -/
@[stacks 08YT "regular derived object"]
noncomputable abbrev regularObject : DerivedCategory (ModuleCat (targetRing k)) :=
  ModuleCat.single0Functor.obj (ModuleCat.of (targetRing k) (targetRing k))

/-- The defining quotient relation is `x * y = 0`. -/
@[stacks 08YT "quotient relation xy = 0"]
theorem x_mul_y_eq_zero : x k * y k = 0 := sorry

/-- Commutativity gives the symmetric relation `y * x = 0`. -/
@[stacks 08YT "quotient relation yx = 0"]
theorem y_mul_x_eq_zero : y k * x k = 0 := sorry

section Nontrivial

variable [Nontrivial k]

/-- Remark 15.60.4 (Warning) (1): restricting `N` to `k[x, y]` before tensoring with `N'`
produces the derived one-variable Koszul stage on `x`. -/
@[stacks 08YT "(1) restricted quotient tensor regular object"]
theorem quotientRestrictedTensorRegular_iso_koszulStage :
    IsIsomorphic
      (((ModuleCat.restrictScalars (algebraMap (baseRing k) (targetRing k))).mapDerivedCategory.obj
          (quotientObject k)) ⊗[baseRing k]^L[targetRing k] (regularObject k))
      ((KoszulComplex.PowerTower.derivedSystem (fun _ : Fin 1 ↦ x k)).obj (op 0)) := sorry

/-- Remark 15.60.4 (Warning) (2): restricting `N'` before tensoring with `N` produces
`N[1] ⊞ N`. -/
@[stacks 08YT "(2) restricted regular tensor quotient object"]
theorem regularRestrictedTensorQuotient_iso_shiftBiproduct :
    IsIsomorphic
      (((ModuleCat.restrictScalars (algebraMap (baseRing k) (targetRing k))).mapDerivedCategory.obj
          (regularObject k)) ⊗[baseRing k]^L[targetRing k] (quotientObject k))
      ((quotientObject k)⟦(1 : ℤ)⟧ ⊞ (quotientObject k)) := sorry

/-- Remark 15.60.4 (Warning) (3): the two choices of which factor supplies the target-ring
module structure yield nonisomorphic derived tensor objects. -/
@[stacks 08YT "(3) nonisomorphic change-of-rings tensor objects"]
theorem not_isomorphic :
    ¬ IsIsomorphic
      (((ModuleCat.restrictScalars (algebraMap (baseRing k) (targetRing k))).mapDerivedCategory.obj
          (quotientObject k)) ⊗[baseRing k]^L[targetRing k] (regularObject k))
      (((ModuleCat.restrictScalars (algebraMap (baseRing k) (targetRing k))).mapDerivedCategory.obj
          (regularObject k)) ⊗[baseRing k]^L[targetRing k] (quotientObject k)) := sorry

end Nontrivial

end CategoryTheory.DerivedTensorChangeOfRings.Counterexample
