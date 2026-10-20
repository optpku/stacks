module

public import Mathlib.Algebra.Divisibility.Units
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Data.Finite.Defs
public import ReasLib.RingTheory.CohenMacaulay.Module
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Presentation
public import ReasLib.RingTheory.LocalRing.HilbertFunction

/-!
# One-dimensional Cohen–Macaulay local rings of embedding dimension two

A cotangent linear form relatively prime to an eventual homogeneous relation
lifts to a regular element, controls maximal-ideal powers, and determines the
relation ideal and Hilbert function.
-/

@[expose] public section

universe u

open IsLocalRing MvPolynomial
open Ideal.AssociatedGraded

namespace MvPolynomial

/-- The two-variable linear form with coefficients `α` and `β` is `C α * X 0 + C β * X 1`. -/
noncomputable def linearForm {k : Type u} [CommRing k] (α β : k) : MvPolynomial (Fin 2) k :=
  C α * X 0 + C β * X 1

/-- A two-variable linear form vanishes if and only if both coefficients vanish. -/
theorem linearForm_eq_zero_iff {k : Type u} [Field k] (α β : k) :
    linearForm α β = 0 ↔ α = 0 ∧ β = 0 := sorry

/-- Every two-variable linear form is homogeneous of degree one. -/
theorem linearForm_isHomogeneous {k : Type u} [CommRing k] (α β : k) :
    (linearForm α β).IsHomogeneous 1 := sorry

end MvPolynomial

namespace IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- The cotangent class of `z` is the linear combination with coefficients `α` and `β`
of the cotangent classes of the two elements in `x`. -/
def IsLinearFormClass (x : Fin 2 → maximalIdeal A) (α β : ResidueField A)
    (z : maximalIdeal A) : Prop :=
  (maximalIdeal A).toCotangent z =
    α • (maximalIdeal A).toCotangent (x 0) + β • (maximalIdeal A).toCotangent (x 1)

/-- The cotangent linear-form condition is equivalent to equality of the associated-graded
evaluation of the polynomial linear form with the degree-one class of `z`. -/
theorem isLinearFormClass_iff_degreeOne (x : Fin 2 → maximalIdeal A)
    (α β : ResidueField A) (z : maximalIdeal A) :
    IsLinearFormClass x α β z ↔
      Presentation.map x (linearForm α β) = degreeOne z := sorry

/-- In a one-dimensional Noetherian Cohen–Macaulay local ring of embedding dimension two,
a lift of a cotangent linear form relatively prime to the eventual homogeneous relation
is a nonzerodivisor. -/
theorem isSMulRegular_of_isLinearFormClass [IsNoetherianRing A] [Module.CohenMacaulay A A]
    (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A)
    {F : MvPolynomial (Fin 2) (ResidueField A)}
    (hF : IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F)
    (z : maximalIdeal A) (α β : ResidueField A) (hz : IsLinearFormClass x α β z)
    (hcoprime : IsRelPrime (linearForm α β) F) :
    IsSMulRegular A (z : A) := sorry

/-- In a one-dimensional Noetherian Cohen–Macaulay local ring of embedding dimension two,
a lift `z` of a cotangent linear form relatively prime to the eventual relation `F` satisfies
`maximalIdeal A ^ n = Ideal.span {z} ^ (n + 1 - F.totalDegree) *
maximalIdeal A ^ (F.totalDegree - 1)` for all sufficiently large `n`. -/
theorem maximalIdeal_pow_eq_span_pow_mul_pow_eventually [IsNoetherianRing A]
    [Module.CohenMacaulay A A] (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A)
    {F : MvPolynomial (Fin 2) (ResidueField A)}
    (hF : IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F)
    (z : maximalIdeal A) (α β : ResidueField A) (hz : IsLinearFormClass x α β z)
    (hcoprime : IsRelPrime (linearForm α β) F) :
    ∃ N ≥ F.totalDegree, ∀ n ≥ N,
      maximalIdeal A ^ n =
        Ideal.span {(z : A)} ^ (n + 1 - F.totalDegree) *
          maximalIdeal A ^ (F.totalDegree - 1) := sorry

/-- A one-dimensional Noetherian Cohen–Macaulay local ring of embedding dimension two
with infinite residue field has an element whose cotangent linear form is relatively prime
to the eventual homogeneous relation. -/
theorem exists_isLinearFormClass_isRelPrime [IsNoetherianRing A] [Module.CohenMacaulay A A]
    [Infinite (ResidueField A)] (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A)
    {F : MvPolynomial (Fin 2) (ResidueField A)}
    (hF : IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F) :
    ∃ (z : maximalIdeal A) (α β : ResidueField A),
      IsLinearFormClass x α β z ∧ IsRelPrime (linearForm α β) F := sorry

/-- In a one-dimensional Noetherian Cohen–Macaulay local ring of embedding dimension two,
a lift `z` of a cotangent linear form relatively prime to the eventual relation `F` satisfies
the maximal-ideal power formula for every `n ≥ F.totalDegree`. -/
theorem maximalIdeal_pow_eq_span_pow_mul_pow [IsNoetherianRing A] [Module.CohenMacaulay A A]
    (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A)
    {F : MvPolynomial (Fin 2) (ResidueField A)}
    (hF : IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F)
    (z : maximalIdeal A) (α β : ResidueField A) (hz : IsLinearFormClass x α β z)
    (hcoprime : IsRelPrime (linearForm α β) F) {n : ℕ} (hn : F.totalDegree ≤ n) :
    maximalIdeal A ^ n =
      Ideal.span {(z : A)} ^ (n + 1 - F.totalDegree) *
        maximalIdeal A ^ (F.totalDegree - 1) := sorry

/-- In a one-dimensional Noetherian Cohen–Macaulay local ring of embedding dimension two,
the existence of a cotangent linear form relatively prime to the eventual homogeneous
relation implies that the associated-graded relation ideal is generated by that relation. -/
theorem associatedGradedRelIdeal_eq_span [IsNoetherianRing A] [Module.CohenMacaulay A A]
    (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A)
    {F : MvPolynomial (Fin 2) (ResidueField A)}
    (hF : IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F)
    (z : maximalIdeal A) (α β : ResidueField A) (hz : IsLinearFormClass x α β z)
    (hcoprime : IsRelPrime (linearForm α β) F) :
    associatedGradedRelIdeal x = Ideal.span {F} := sorry

/-- In a one-dimensional Noetherian local ring of embedding dimension two, a principal
associated-graded relation ideal generated by the eventual homogeneous relation `F` gives
Hilbert function `min (n + 1) F.totalDegree` in every positive degree `n`. -/
theorem associatedGradedHilbertFn_eq_min_succ_totalDegree_of_span [IsNoetherianRing A]
    (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A)
    {F : MvPolynomial (Fin 2) (ResidueField A)}
    (hF : IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F)
    (hI : associatedGradedRelIdeal x = Ideal.span {F}) {n : ℕ} (hn : 1 ≤ n) :
    associatedGradedHilbertFn A n = min (n + 1) F.totalDegree := sorry

/-- In a one-dimensional Noetherian Cohen–Macaulay local ring of embedding dimension two,
a cotangent linear form relatively prime to the eventual homogeneous relation `F` implies
that the Hilbert function in every positive degree `n` is `min (n + 1) F.totalDegree`. -/
theorem associatedGradedHilbertFn_eq_min_succ_totalDegree [IsNoetherianRing A]
    [Module.CohenMacaulay A A] (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A)
    {F : MvPolynomial (Fin 2) (ResidueField A)}
    (hF : IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F)
    (z : maximalIdeal A) (α β : ResidueField A) (hz : IsLinearFormClass x α β z)
    (hcoprime : IsRelPrime (linearForm α β) F) {n : ℕ} (hn : 1 ≤ n) :
    associatedGradedHilbertFn A n = min (n + 1) F.totalDegree := sorry

/-- In a one-dimensional Noetherian local ring of embedding dimension two with principal
associated-graded relation ideal generated by `F`, the Hilbert function is `n + 1`
whenever `1 ≤ n < F.totalDegree`. -/
theorem associatedGradedHilbertFn_eq_succ_of_lt_totalDegree [IsNoetherianRing A]
    (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A)
    {F : MvPolynomial (Fin 2) (ResidueField A)}
    (hF : IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F)
    (hI : associatedGradedRelIdeal x = Ideal.span {F}) {n : ℕ} (hn : 1 ≤ n)
    (hnd : n < F.totalDegree) :
    associatedGradedHilbertFn A n = n + 1 := sorry

/-- In a one-dimensional Noetherian local ring of embedding dimension two with principal
associated-graded relation ideal generated by `F`, the Hilbert function is `F.totalDegree`
in every positive degree `n ≥ F.totalDegree`. -/
theorem associatedGradedHilbertFn_eq_totalDegree_of_ge [IsNoetherianRing A]
    (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A)
    {F : MvPolynomial (Fin 2) (ResidueField A)}
    (hF : IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F)
    (hI : associatedGradedRelIdeal x = Ideal.span {F}) {n : ℕ} (hn : 1 ≤ n)
    (hnd : F.totalDegree ≤ n) :
    associatedGradedHilbertFn A n = F.totalDegree := sorry

end IsLocalRing
