/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Basic
public import ReasLib.RingTheory.Extension.Presentation.Localization

@[expose] public section

/-!
# Local Data of Relative Global Complete Intersection Presentations

This leaf owns the prime-local relation sequence attached to a fixed relative
global complete intersection presentation.  The ordering of the relations is
part of the presentation data, so these statements belong here rather than at
the intrinsic algebra or ring-hom layer.

@stack 00SV
-/

noncomputable section

universe u v

namespace Algebra

namespace Presentation

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {n c : ℕ}

namespace IsRelativeGlobalCompleteIntersection

/-- The ordered relations of a relative global complete intersection
presentation form a regular sequence at every target prime. -/
@[stacks 00SV "localized relations of a relative global complete intersection are regular"]
theorem relations_isRegular_atPrime
    {P : Presentation R S (Fin n) (Fin c)}
    (hP : P.IsRelativeGlobalCompleteIntersection) (q : PrimeSpectrum S) :
    RingTheory.Sequence.IsRegular
      (P.sourceLocalRingAt q)
      (P.relationsAtPrime q) := sorry

/-- Every quotient by an initial segment of the localized ordered relations is
flat over the base ring. -/
@[stacks 00SV "localized relation prefix quotients are flat"]
theorem relationPrefixQuotient_flat_atPrime
    {P : Presentation R S (Fin n) (Fin c)}
    (hP : P.IsRelativeGlobalCompleteIntersection) (q : PrimeSpectrum S) (i : Fin c) :
    Module.Flat R
      (P.sourceLocalRingAt q ⧸
        Algebra.Presentation.relationsAtPrime.prefixIdeal P q i) := sorry

/-- The classes of the displayed relations form a basis of the canonical
cotangent module of the presentation. -/
@[stacks 00SV "relative global complete intersection cotangent basis"]
theorem exists_basisCotangent
    {P : Presentation R S (Fin n) (Fin c)}
    (hP : P.IsRelativeGlobalCompleteIntersection) :
    ∃ b : Module.Basis (Fin c) S P.toExtension.Cotangent,
      ∀ i, b i = Extension.Cotangent.mk ⟨P.relation i, P.relation_mem_ker i⟩ := sorry

/-- For the naive presentation of an explicit polynomial quotient, the
displayed relation classes form a basis of the quotient-ideal cotangent
module. -/
@[stacks 00SV "naive quotient cotangent basis"]
theorem exists_basisCotangent_naive
    {f : Fin c → MvPolynomial (Fin n) R}
    (hP :
      (Presentation.naive : Presentation R
        (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
        (Fin n) (Fin c)).IsRelativeGlobalCompleteIntersection) :
    ∃ b : Module.Basis (Fin c)
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
      (Ideal.span (Set.range f)).Cotangent,
      ∀ i, b i = Ideal.toCotangent _
        ⟨f i, Ideal.subset_span (Set.mem_range_self i)⟩ := sorry

end IsRelativeGlobalCompleteIntersection

end Presentation

end Algebra
