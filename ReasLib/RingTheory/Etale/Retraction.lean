module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Faithfully flat étale retractions

A commutative ring has the faithfully flat étale retraction property when every
faithfully flat étale algebra over it admits an algebra retraction. This
property passes to quotient rings.
-/

@[expose] public section

universe u

namespace Algebra

/-- A commutative ring has the faithfully flat étale retraction property when
every faithfully flat étale algebra over it admits a retraction. -/
@[mk_iff]
class HasFaithfullyFlatEtaleRetraction (R : Type u) [CommRing R] : Prop where
  /-- Every faithfully flat étale algebra over `R` admits an `R`-algebra
  retraction. -/
  nonempty_retraction {S : Type u} [CommRing S] [Algebra R S] [Etale R S]
    [Module.FaithfullyFlat R S] : Nonempty (S →ₐ[R] R)

namespace HasFaithfullyFlatEtaleRetraction

variable {R : Type u} [CommRing R]

/-- The retraction property is the statement that every faithfully flat étale
algebra admits an algebra retraction. -/
theorem spec :
    HasFaithfullyFlatEtaleRetraction R ↔
      ∀ {S : Type u} [CommRing S] [Algebra R S] [Etale R S]
        [Module.FaithfullyFlat R S], Nonempty (S →ₐ[R] R) := sorry

/-- A faithfully flat étale algebra over a ring with the retraction property
admits an algebra retraction. -/
theorem nonempty_algHom [HasFaithfullyFlatEtaleRetraction R] {S : Type u}
    [CommRing S] [Algebra R S] [Etale R S] [Module.FaithfullyFlat R S] :
    Nonempty (S →ₐ[R] R) := sorry

/-- The retraction property is equivalent to every faithfully flat étale ring
map admitting a ring-homomorphism retraction. -/
theorem iff_ringHom :
    HasFaithfullyFlatEtaleRetraction R ↔
      ∀ {S : Type u} [CommRing S] (f : R →+* S),
        f.Etale → f.FaithfullyFlat → ∃ g : S →+* R, g.comp f = RingHom.id R := sorry

/-- The faithfully flat étale retraction property passes to quotient rings. -/
instance quotient [HasFaithfullyFlatEtaleRetraction R] (I : Ideal R) :
    HasFaithfullyFlatEtaleRetraction (R ⧸ I) := sorry

end HasFaithfullyFlatEtaleRetraction

end Algebra
