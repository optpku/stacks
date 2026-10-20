module

public import ReasLib.RingTheory.LocalRing.HilbertFunction
import StacksCheckRecall

/-!
# Hilbert function of a one-dimensional embedding-dimension-two local ring

This file records the five source clauses of Exercise 111.28.7 as typed checks
of their reusable mathematical declarations.
-/

@[expose] public section

universe u

open Filter IsLocalRing MvPolynomial

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/- Exercise 111.28.7 (1): if `A` is a Noetherian local ring of dimension `1` and embedding
dimension `2`, and `x` generates the maximal ideal, then there is a homogeneous `F` in
`k[X, Y]` such that the presentation kernel `I` satisfies `I ≤ (F)` with equality in all
sufficiently high degrees. -/
@[stacks 02EL] #check (IsLocalRing.exists_homogeneousEventuallySpan :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A],
    ringKrullDim A = 1 →
    Module.finrank (ResidueField A) (CotangentSpace A) = 2 →
    (x : Fin 2 → maximalIdeal A) →
    Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A →
    ∃ F, MvPolynomial.IsHomogeneousEventuallySpan
      (IsLocalRing.associatedGradedRelIdeal x) F)

/- Exercise 111.28.7 (2): the residue-field Hilbert function of such a ring satisfies
`associatedGradedHilbertFn A n ≤ n + 1`. -/
@[stacks 02EL] #check (IsLocalRing.associatedGradedHilbertFn_le_succ :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A],
    ringKrullDim A = 1 →
    Module.finrank (ResidueField A) (CotangentSpace A) = 2 →
    (n : ℕ) → IsLocalRing.associatedGradedHilbertFn A n ≤ n + 1)

/- Exercise 111.28.7 (3): if `associatedGradedHilbertFn A n < n + 1`, then
`F.totalDegree ≤ n`. -/
@[stacks 02EL] #check
  (IsLocalRing.associatedGradedHilbertFn_lt_succ_imp_totalDegree_le :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A],
      ringKrullDim A = 1 →
      Module.finrank (ResidueField A) (CotangentSpace A) = 2 →
      (x : Fin 2 → maximalIdeal A) →
      Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A →
      {F : MvPolynomial (Fin 2) (ResidueField A)} →
      MvPolynomial.IsHomogeneousEventuallySpan
        (IsLocalRing.associatedGradedRelIdeal x) F →
      {n : ℕ} → IsLocalRing.associatedGradedHilbertFn A n < n + 1 →
      F.totalDegree ≤ n)

/- Exercise 111.28.7 (4): if `associatedGradedHilbertFn A n < n + 1`, then
`associatedGradedHilbertFn A (n + 1) ≤ associatedGradedHilbertFn A n`. -/
@[stacks 02EL] #check (IsLocalRing.associatedGradedHilbertFn_lt_succ_antitone :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A],
    ringKrullDim A = 1 →
    Module.finrank (ResidueField A) (CotangentSpace A) = 2 →
    {n : ℕ} → IsLocalRing.associatedGradedHilbertFn A n < n + 1 →
    IsLocalRing.associatedGradedHilbertFn A (n + 1) ≤
      IsLocalRing.associatedGradedHilbertFn A n)

/- Exercise 111.28.7 (5): `associatedGradedHilbertFn A n = F.totalDegree` for all
sufficiently large `n`. -/
@[stacks 02EL] #check
  (IsLocalRing.associatedGradedHilbertFn_eventually_eq_totalDegree :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A],
      ringKrullDim A = 1 →
      Module.finrank (ResidueField A) (CotangentSpace A) = 2 →
      (x : Fin 2 → maximalIdeal A) →
      Ideal.span (Set.range fun i ↦ (x i : A)) = maximalIdeal A →
      {F : MvPolynomial (Fin 2) (ResidueField A)} →
      MvPolynomial.IsHomogeneousEventuallySpan
        (IsLocalRing.associatedGradedRelIdeal x) F →
      ∀ᶠ n in atTop, IsLocalRing.associatedGradedHilbertFn A n = F.totalDegree)
