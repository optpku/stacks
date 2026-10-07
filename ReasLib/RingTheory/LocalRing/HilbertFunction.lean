module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Presentation
public import ReasLib.RingTheory.MvPolynomial.EventualPrincipal

/-!
# Hilbert functions of one-dimensional local rings

This file owns the residue-field Hilbert function, the relation ideal of a
two-generator associated-graded presentation, and the embedding-dimension-two
consequences for that Hilbert function.
-/

@[expose] public section

noncomputable section

universe u

open Filter MvPolynomial

namespace IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- The residue-field Hilbert function sends a degree to the finrank of the
corresponding maximal-ideal associated-graded piece. -/
def associatedGradedHilbertFn (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) : ℕ :=
  Module.finrank (ResidueField A) (Ideal.AssociatedGraded.piece (maximalIdeal A) A n)

/-- The degree-zero value of the residue-field Hilbert function is one. -/
theorem associatedGradedHilbertFn_zero (A : Type u) [CommRing A] [IsLocalRing A] :
    associatedGradedHilbertFn A 0 = 1 := sorry

/-- Every maximal-ideal associated-graded piece of a Noetherian local ring is
finite-dimensional over its residue field. -/
instance finiteDimensional_associatedGradedPiece [IsNoetherianRing A] (n : ℕ) :
    FiniteDimensional (ResidueField A)
      (Ideal.AssociatedGraded.piece (maximalIdeal A) A n) := sorry

/-- The relation ideal is the kernel of the polynomial presentation map
determined by a two-element family in the maximal ideal. -/
def associatedGradedRelIdeal (x : Fin 2 → maximalIdeal A) :
    Ideal (MvPolynomial (Fin 2) (ResidueField A)) :=
  RingHom.ker (Ideal.AssociatedGraded.Presentation.map x)

/-- Membership in the relation ideal is equivalent to vanishing under the
associated-graded polynomial presentation map. -/
theorem mem_associatedGradedRelIdeal (x : Fin 2 → maximalIdeal A)
    (p : MvPolynomial (Fin 2) (ResidueField A)) :
    p ∈ associatedGradedRelIdeal x ↔
      Ideal.AssociatedGraded.Presentation.map x p = 0 := sorry

/-- The relation ideal is closed under taking homogeneous components. -/
theorem associatedGradedRelIdeal_isHomogeneous (x : Fin 2 → maximalIdeal A)
    (p : MvPolynomial (Fin 2) (ResidueField A)) (n : ℕ) :
    p ∈ associatedGradedRelIdeal x →
      homogeneousComponent n p ∈ associatedGradedRelIdeal x := sorry

/-- A one-dimensional Noetherian local ring with two-dimensional cotangent
space has an eventually homogeneous principal relation ideal. -/
theorem exists_homogeneousEventuallySpan (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A) :
    ∃ F, IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F := sorry

/-- Under the same hypotheses, the residue-field Hilbert function is bounded
above by the dimension of the degree-`n` piece of a two-variable polynomial
ring. -/
theorem associatedGradedHilbertFn_le_succ (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2) (n : ℕ) :
    associatedGradedHilbertFn A n ≤ n + 1 := sorry

/-- If the Hilbert function has a strict deficit in degree `n`, the total degree
of an eventual homogeneous generator is at most `n`. -/
theorem associatedGradedHilbertFn_lt_succ_imp_totalDegree_le (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A)
    {F : MvPolynomial (Fin 2) (ResidueField A)}
    (hF : IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F) {n : ℕ}
    (hn : associatedGradedHilbertFn A n < n + 1) :
    F.totalDegree ≤ n := sorry

/-- A strict deficit in degree `n` makes the next Hilbert value no larger than
the value in degree `n`. -/
theorem associatedGradedHilbertFn_lt_succ_antitone (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2) {n : ℕ}
    (hn : associatedGradedHilbertFn A n < n + 1) :
    associatedGradedHilbertFn A (n + 1) ≤ associatedGradedHilbertFn A n := sorry

/-- The residue-field Hilbert function eventually equals the total degree of an
eventual homogeneous generator of the relation ideal. -/
theorem associatedGradedHilbertFn_eventually_eq_totalDegree (hdim : ringKrullDim A = 1)
    (hemb : Module.finrank (ResidueField A) (CotangentSpace A) = 2)
    (x : Fin 2 → maximalIdeal A)
    (hx : Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A)
    {F : MvPolynomial (Fin 2) (ResidueField A)}
    (hF : IsHomogeneousEventuallySpan (associatedGradedRelIdeal x) F) :
    ∀ᶠ n in atTop, associatedGradedHilbertFn A n = F.totalDegree := sorry

end IsLocalRing
