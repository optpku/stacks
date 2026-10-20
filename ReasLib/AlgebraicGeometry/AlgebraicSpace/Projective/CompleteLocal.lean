module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AdicThickening

/-!
# Projectivity over complete Noetherian local rings

A proper algebraic space over the spectrum of a complete Noetherian local ring,
with special fibre of dimension at most one, is represented by a scheme
H-projective over the base.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A proper algebraic space over the spectrum of a complete Noetherian local ring
whose special fibre has dimension at most one is represented by a scheme
H-projective over that spectrum. The special fibre is the first adic stage
for the maximal ideal. -/
@[stacks 0AE7]
theorem isScheme_hProjective_of_proper_specialFiber_dimension_le_one
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (X : AlgebraicSpace (Spec (CommRingCat.of A))) [Proper (SchemeRealization.toBase X)]
    (hdim : dimension (AdicThickening.stage X (IsLocalRing.maximalIdeal A) 1) ≤ 1) :
    ∃ (T : Over (Spec (CommRingCat.of A))),
      Nonempty (X ≅ ofOver T) ∧ HProjective T.hom :=
  sorry

/-- A cartesian successor ladder of algebraic spaces over the maximal-ideal adic
spectra of a complete local Noetherian ring, with proper first stage of dimension
at most one, is induced by a scheme H-projective over the ring. The comparison
maps commute with the successor maps and exhibit every stage as a base change. -/
@[stacks 0E7R]
theorem exists_algebraizingProjective_of_dimension_le_one
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (X : ℕ+ → AlgebraicSpace (Spec (CommRingCat.of A)))
    (succ : ∀ n, X n ⟶ X (n + 1))
    (toSpec : ∀ n, X n ⟶ AdicThickening.spec (IsLocalRing.maximalIdeal A) n)
    (h_pb : ∀ n,
      IsPullback (succ n) (toSpec n) (toSpec (n + 1))
        (AdicThickening.specTransition (IsLocalRing.maximalIdeal A) n))
    [Proper (toSpec 1)] (hdim : dimension (X 1) ≤ 1) :
    ∃ (W : Scheme.{u}) (π : W ⟶ Spec (CommRingCat.of A))
      (e : ∀ n, X n ⟶ ofOver (Over.mk π)),
      HProjective π ∧ (∀ n, e n = succ n ≫ e (n + 1)) ∧
        ∀ n, IsPullback (e n) (toSpec n)
          (SchemeRealization.toBase (ofOver (Over.mk π)))
          (SchemeRealization.toBase (AdicThickening.spec (IsLocalRing.maximalIdeal A) n)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
