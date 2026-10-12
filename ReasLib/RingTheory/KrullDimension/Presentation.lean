/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.KrullDimension.Polynomial

@[expose] public section

/-!
# Krull Dimension Bounds from Finite Presentations

The statements in this leaf concern a chosen finite presentation over a
field.  They are independent of complete-intersection predicates and can be
reused whenever a presentation supplies generators and relations.

@stack 00ST
-/

universe u v w t

namespace MvPolynomial

variable {k : Type u} {ι : Type w} {σ : Type t} [Field k]

/-- A nonempty quotient of affine space over a field satisfies the
Krull-height lower bound determined by its variables and defining relations.
The nonempty-spectrum hypothesis is necessary because the zero quotient has
Krull dimension `⊥`. -/
@[stacks 00ST "polynomial quotient Krull-height lower bound"]
theorem card_vars_le_ringKrullDim_quotient_add_card_relations
    [Finite ι] [Finite σ] (f : σ → MvPolynomial ι k)
    (hQ : Nonempty (PrimeSpectrum (MvPolynomial ι k ⧸ Ideal.span (Set.range f)))) :
    (Nat.card ι : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial ι k ⧸ Ideal.span (Set.range f)) + Nat.card σ := sorry

end MvPolynomial

namespace Algebra.Presentation

variable {k : Type u} {S : Type v} {ι : Type w} {σ : Type t}
variable [Field k] [CommRing S] [Algebra k S]

/-- A nonempty algebra with a finite presentation over a field satisfies the
Krull-height lower bound determined by its generators and relations. -/
@[stacks 00ST "finite presentation Krull-height lower bound"]
theorem card_generators_le_ringKrullDim_add_card_relations
    [Finite ι] [Finite σ] (P : Presentation k S ι σ)
    (hS : Nonempty (PrimeSpectrum S)) :
    (Nat.card ι : WithBot ℕ∞) ≤ ringKrullDim S + Nat.card σ := sorry

/-- An upper bound by the dimension of a finite presentation over a field is
sharp whenever the target spectrum is nonempty. -/
@[stacks 00ST "finite presentation dimension equality"]
theorem ringKrullDim_eq_dimension_of_le
    [Finite ι] [Finite σ] (P : Presentation k S ι σ)
    (hS : Nonempty (PrimeSpectrum S)) (hupper : ringKrullDim S ≤ P.dimension) :
    ringKrullDim S = P.dimension := sorry

end Algebra.Presentation
