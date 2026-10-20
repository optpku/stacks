module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Projective.CompleteLocal
import StacksCheckRecall

/-!
# Algebraization of dimension ≤ 1 cartesian ladders of algebraic spaces

A cartesian successor ladder of algebraic spaces over the adic spectra of a
complete local Noetherian ring, with proper first stage of dimension at most
one, algebraizes to a projective morphism of schemes.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 76.43.5: Let `(A, m, κ)` be a complete local Noetherian ring. Set
`S = Spec(A)` and `S_n = Spec(A ⧸ m^n)`. Given a commutative diagram of algebraic
spaces over `S` with cartesian successor squares `X n ⟶ X (n + 1)` over
`S_n ⟶ S_{n+1}`, if `toSpec 1` is proper and `dimension (X 1) ≤ 1`, then there
exists a projective morphism of schemes `π : W ⟶ S` together with identifications
`X n ≅ W ×_S S_n` compatible with the successor maps. -/
@[stacks 0E7R] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_algebraizingProjective_of_dimension_le_one :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (X : ℕ+ → AlgebraicSpace (Spec (CommRingCat.of A)))
    (succ : ∀ n, X n ⟶ X (n + 1))
    (toSpec : ∀ n, X n ⟶ AdicThickening.spec (IsLocalRing.maximalIdeal A) n)
    (h_pb : ∀ n,
      IsPullback (succ n) (toSpec n) (toSpec (n + 1))
        (AdicThickening.specTransition (IsLocalRing.maximalIdeal A) n))
    [Proper (toSpec 1)] (hdim : dimension (X 1) ≤ 1),
    ∃ (W : Scheme.{u}) (π : W ⟶ Spec (CommRingCat.of A))
      (e : ∀ n, X n ⟶ ofOver (Over.mk π)),
      HProjective π ∧ (∀ n, e n = succ n ≫ e (n + 1)) ∧
        ∀ n, IsPullback (e n) (toSpec n)
          (SchemeRealization.toBase (ofOver (Over.mk π)))
          (SchemeRealization.toBase (AdicThickening.spec (IsLocalRing.maximalIdeal A) n)))
