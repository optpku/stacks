/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Smooth.AtPrime

@[expose] public section

/-!
# Singular Loci and Ideals

The nonsmooth locus of a morphism of affine schemes and the radical ideal
that cuts it out.

@stack 07C5
-/

universe u v w

namespace Algebra

open PrimeSpectrum

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]

/-- The nonsmooth locus of `Spec(A) → Spec(R)`, consisting of primes where
`SmoothAtPrime R A` fails. -/
@[stacks 07C5 "nonsmooth locus"]
def nonsmoothLocus : Set (PrimeSpectrum A) := { q | ¬ SmoothAtPrime R A q }

/-- The set of primes where an algebra is smooth in the Stacks-style local sense is open. -/
@[stacks 07C5 "open smooth locus"]
theorem isOpen_smoothAtPrime :
    IsOpen { q : PrimeSpectrum A | SmoothAtPrime R A q } := sorry

/-- The nonsmooth locus is closed. -/
@[stacks 07C5 "closed nonsmooth locus"]
theorem isClosed_nonsmoothLocus : IsClosed (nonsmoothLocus R A) := sorry

/-- For finitely presented algebras, the nonsmooth locus is the complement of mathlib's
`smoothLocus`. -/
@[stacks 07C5 "nonsmooth locus complement"]
theorem nonsmoothLocus_eq_compl_smoothLocus [FinitePresentation R A] :
    nonsmoothLocus R A = (smoothLocus R A)ᶜ := sorry

/-- Definition 16.2.1: the singular ideal `H[A⁄R]` is the radical ideal cutting out the
nonsmooth locus of `Spec(A) → Spec(R)`. -/
@[stacks 07C5]
def singularIdeal : Ideal A :=
  vanishingIdeal (nonsmoothLocus R A)

end Algebra

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The singular ideal of the target of an `R`-algebra map, relative to its induced
`A`-algebra structure. -/
abbrev singularIdeal (f : A →ₐ[R] B) : Ideal B :=
  @Algebra.singularIdeal A B _ _ f.toAlgebra

end AlgHom

namespace RingHom

variable (R : Type u) {A : Type v} {Λ : Type w}
variable [CommRing R] [CommRing A] [CommRing Λ] [Algebra R A]

/-- Situation 16.9.1: the singular ideal of an `R`-algebra `A`, transported
along a ring map `A → Λ` and made radical in the target. -/
@[stacks 07F7 "transported singular ideal"]
def singularIdealIn (g : A →+* Λ) : Ideal Λ :=
  Ideal.radical (Ideal.map g (Algebra.singularIdeal R A))

end RingHom

namespace AlgHom

variable {R : Type u} {A : Type v} {Λ : Type w}
variable [CommRing R] [CommRing A] [CommRing Λ] [Algebra R A] [Algebra R Λ]

/-- The singular ideal of `A` over `R`, transported along an `R`-algebra map and made radical
in its target. -/
@[stacks 07F7 "algebra-map singular ideal bridge"]
abbrev singularIdealIn (f : A →ₐ[R] Λ) : Ideal Λ :=
  RingHom.singularIdealIn R f.toRingHom

/-- An algebra map is smooth at the prime pulled back from its target exactly
when its transported singular ideal is not contained in that target prime. -/
@[stacks 07F7 "transported singular ideal criterion"]
theorem smoothAtPrime_comap_iff_not_singularIdealIn_le
    (f : A →ₐ[R] Λ) (q : PrimeSpectrum Λ) :
    Algebra.SmoothAtPrime R A (PrimeSpectrum.comap f.toRingHom q) ↔
      ¬ f.singularIdealIn ≤ q.asIdeal := sorry

end AlgHom

namespace SingularIdealNotation

variable (R : Type u) (A : Type v) (Λ : Type w)
variable [CommRing R] [CommRing A] [CommRing Λ] [Algebra R A] [Algebra A Λ]

@[inherit_doc RingHom.singularIdealIn]
scoped notation:max "h(" A "⁄" R ", " Λ ")" =>
  RingHom.singularIdealIn R (algebraMap A Λ)

/-- Notation for the singular ideal of an `R`-algebra `A`. -/
scoped notation:max "H[" A "⁄" R "]" => Algebra.singularIdeal R A

end SingularIdealNotation

open scoped SingularIdealNotation

namespace Algebra

open PrimeSpectrum

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]

/-- The singular ideal is radical. -/
@[stacks 07C5 "radical singular ideal"]
theorem singularIdeal_isRadical :
    (H[A⁄R]).IsRadical := sorry

/-- The zero locus of the singular ideal is the nonsmooth locus. -/
@[stacks 07C5 "singular ideal zero locus"]
theorem zeroLocus_singularIdeal :
    zeroLocus (H[A⁄R]) = nonsmoothLocus R A := sorry

/-- A prime contains the singular ideal exactly when the algebra is not smooth at that prime. -/
@[stacks 07C5 "singular ideal membership criterion"]
theorem singularIdeal_le_iff_not_smoothAtPrime (q : PrimeSpectrum A) :
    H[A⁄R] ≤ q.asIdeal ↔ ¬ SmoothAtPrime R A q := sorry

/-- Smoothness at a prime is equivalent to that prime avoiding the singular ideal. -/
@[stacks 07C5 "smooth locus singular ideal criterion"]
theorem smoothAtPrime_iff_not_singularIdeal_le (q : PrimeSpectrum A) :
    SmoothAtPrime R A q ↔ ¬ H[A⁄R] ≤ q.asIdeal := sorry

/-- An extended ideal lies in the singular ideal exactly when every prime avoiding the
extended ideal is a smooth point. -/
theorem map_le_singularIdeal_iff (I : Ideal R) :
    Ideal.map (algebraMap R A) I ≤ H[A⁄R] ↔
      ∀ q : PrimeSpectrum A,
        ¬ Ideal.map (algebraMap R A) I ≤ q.asIdeal → SmoothAtPrime R A q := sorry

/-- For finitely presented algebras, the zero locus of the singular ideal is the complement of
mathlib's `smoothLocus`. -/
@[stacks 07C5 "singular ideal smooth locus complement"]
theorem zeroLocus_singularIdeal_eq_compl_smoothLocus [FinitePresentation R A] :
    zeroLocus (H[A⁄R]) = (smoothLocus R A)ᶜ := sorry

/-- A radical ideal whose zero locus is the nonsmooth locus is the singular ideal. -/
@[stacks 07C5 "singular ideal uniqueness"]
theorem singularIdeal_unique {I : Ideal A} (hI : I.IsRadical)
    (hV : zeroLocus I = nonsmoothLocus R A) :
    I = H[A⁄R] := sorry

end Algebra
