/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.UniversallyInjective.Quotient
import ReasLib.LinearAlgebra.QuotientByIdeal.Pi
import Mathlib.Tactic.CrossRefAttribute

/-!
# Matrix maps modulo ideals

@stack 0AS5
@stack 00MX

This leaf specializes the quotient criterion for universally injective linear maps to finite
coordinate modules.  Its closed-fiber companion records the form used by the local
Buchsbaum--Eisenbud argument.
-/

@[expose] public section

universe u

namespace LinearMap

variable {R : Type u} [CommRing R]
variable {m n : ℕ}

/-- A universally injective matrix map remains injective after reducing every matrix entry
modulo an ideal. -/
@[stacks 0AS5 "matrix maps modulo an ideal"]
theorem injective_map_quotient_of_universallyInjective
    (I : Ideal R) (A : Matrix (Fin n) (Fin m) R)
    (hA : UniversallyInjective.{u, u, u, u} A.toLin') :
    Function.Injective ((A.map (Ideal.Quotient.mk I)).toLin') := by
  classical
  let eM := Ideal.Quotient.Pi.quotientLinearEquiv I m
  let eN := Ideal.Quotient.Pi.quotientLinearEquiv I n
  have hquotient :=
    injective_quotientMapByIdeal_of_universallyInjective A.toLin' hA I
  have hcomm
      (x : (Fin m → R) ⧸ (I • (⊤ : Submodule R (Fin m → R)))) :
      (A.map (Ideal.Quotient.mk I)).toLin' (eM x) =
        eN (A.toLin'.quotientMapByIdeal I x) := by
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
        have hcoeff : Ideal.Quotient.Pi.coeffMap I m x = Ideal.Quotient.mk I ∘ x := by
          funext j
          exact Ideal.Quotient.Pi.coeffMap_apply I m x j
        ext i
        simpa only [eM, eN, Ideal.Quotient.Pi.quotientLinearEquiv_apply_mk,
          Ideal.Quotient.Pi.coeffMap_apply, quotientMapByIdeal_apply_mk,
          Matrix.toLin'_apply, hcoeff, Function.comp_apply] using
          (RingHom.map_mulVec (Ideal.Quotient.mk I) A x i).symm
  intro x y hxy
  obtain ⟨x, rfl⟩ := eM.surjective x
  obtain ⟨y, rfl⟩ := eM.surjective y
  apply congrArg eM
  apply hquotient
  apply eN.injective
  rw [← hcomm x, ← hcomm y, hxy]

/-- Universal injectivity after localization at a prime implies injectivity of the corresponding
matrix map on the closed fiber. -/
@[stacks 00MX "closed-fiber matrix specialization"]
theorem injective_closedFiberMatrixMap_of_localized_universallyInjective
    {p : Ideal R} [p.IsPrime] (A : Matrix (Fin n) (Fin m) R)
    (hA : UniversallyInjective.{u, u, u, u}
      ((A.map (algebraMap R (Localization.AtPrime p))).toLin')) :
    Function.Injective
      ((A.map
        ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime p))).comp
          (algebraMap R (Localization.AtPrime p)))).toLin') := by
  simpa only [Matrix.map_map, RingHom.coe_comp, Function.comp_def] using
    injective_map_quotient_of_universallyInjective
      (IsLocalRing.maximalIdeal (Localization.AtPrime p))
      (A.map (algebraMap R (Localization.AtPrime p))) hA

end LinearMap
