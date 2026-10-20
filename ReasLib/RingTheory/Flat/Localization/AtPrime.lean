module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Localization.AtPrime.Relative

/-!
# Prime-Local Criteria for Flat Modules

Local flatness predicates and criteria for modules. Relative prime localizations keep their
induced scalar action inside the predicate, avoiding noncanonical localization instances.
-/

@[expose] public section

universe u v w x

namespace Module

section Absolute

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- Flatness of the localization of an `R`-module at a prime of `R`. -/
@[stacks 00HT "flatness at a prime"]
abbrev Flat.AtPrime (p : PrimeSpectrum R) : Prop :=
  Module.Flat (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M)

/-- Flatness of the localization of an `R`-module at a maximal ideal of `R`. -/
@[stacks 00HT "flatness at a maximal ideal"]
abbrev Flat.AtMaximal (m : MaximalSpectrum R) : Prop :=
  Module.Flat (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal M)

end Absolute

section Relative

variable {R : Type u} [CommSemiring R]
variable {A : Type v} [CommSemiring A] [Algebra R A]
variable {M : Type w} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- Flatness of `LocalizedModule.AtPrime q.asIdeal M` over the local base ring
`Localization.AtPrime (q.asIdeal.under R)`.  The induced action is explicit in the definition
rather than registered as a global instance. -/
@[stacks 00HT "relative flatness at a prime"]
noncomputable abbrev Flat.AtPrimeOver (q : PrimeSpectrum A) : Prop :=
  -- Local declaration justification (instance diamond): the relative localized module action is
  -- selected by the named support API and is intentionally not registered globally.
  letI : Module (Localization.AtPrime (q.asIdeal.under R))
      (LocalizedModule.AtPrime q.asIdeal M) :=
    Localization.AtPrime.Relative.algebraMapModule (R := R) (M := M) q.asIdeal
  Module.Flat (Localization.AtPrime (q.asIdeal.under R))
    (LocalizedModule.AtPrime q.asIdeal M)

/-- Flatness of `LocalizedModule.AtPrime m.asIdeal M` over
`Localization.AtPrime (m.asIdeal.under R)` at a maximal ideal of `A`. -/
@[stacks 00HT "relative flatness at a maximal ideal"]
noncomputable abbrev Flat.AtMaximalOver (m : MaximalSpectrum A) : Prop :=
  -- Local declaration justification (instance diamond): use the same noncanonical relative action
  -- for a maximal prime without polluting global typeclass search.
  letI : Module (Localization.AtPrime (m.asIdeal.under R))
      (LocalizedModule.AtPrime m.asIdeal M) :=
    Localization.AtPrime.Relative.algebraMapModule (R := R) (M := M) m.asIdeal
  Module.Flat (Localization.AtPrime (m.asIdeal.under R))
    (LocalizedModule.AtPrime m.asIdeal M)

end Relative

namespace Flat

section Absolute

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- Flatness is detected after localization at every prime ideal. -/
@[stacks 00HT "flatness is local at primes"]
theorem iff_forall_atPrime :
    Module.Flat R M ↔ ∀ p : PrimeSpectrum R, Module.Flat.AtPrime (M := M) p := sorry

/-- Flatness is detected after localization at every maximal ideal. -/
@[stacks 00HT "flatness is local at maximal ideals"]
theorem iff_forall_atMaximal :
    Module.Flat R M ↔ ∀ m : MaximalSpectrum R, Module.Flat.AtMaximal (M := M) m := sorry

end Absolute

section Relative

variable {R : Type u} [CommSemiring R]
variable {A : Type v} [CommSemiring A] [Algebra R A]
variable {M : Type w} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- Localization of an `A`-module preserves flatness over the base ring `R`. -/
@[stacks 00HT "flatness under localization"]
theorem localizedModule_of_tower (T : Submonoid A) (hM : Module.Flat R M) :
    Module.Flat R (LocalizedModule T M) := sorry

/-- Localization away from an element of `A` preserves flatness over the base ring `R`. -/
@[stacks 00HT "flatness under principal localization"]
theorem away_of_tower (a : A) (hM : Module.Flat R M) :
    Module.Flat R (LocalizedModule.Away a M) := sorry

/-- Flatness over `R` is detected after localizing away from each element of a set that spans the
unit ideal in `A`. -/
@[stacks 00HT "flatness is local on principal opens"]
theorem iff_forall_away_of_span_eq_top {s : Set A} (hs : Ideal.span s = ⊤) :
    Module.Flat R M ↔ ∀ a : s, Module.Flat R (LocalizedModule.Away a.1 M) := sorry

/-- The range-indexed form of the principal-open flatness criterion. -/
@[stacks 00HT "flatness is local on a generated principal-open cover"]
theorem iff_forall_away_of_span_range_eq_top {ι : Type x} (g : ι → A)
    (hg : Ideal.span (Set.range g) = ⊤) :
    Module.Flat R M ↔ ∀ i : ι, Module.Flat R (LocalizedModule.Away (g i) M) := sorry

/-- A flat `R`-module remains flat over `Localization.AtPrime (q.asIdeal.under R)` after
localizing its `A`-module structure at a prime `q` of `A`. -/
@[stacks 00HT "relative flatness at a prime"]
theorem atPrimeOver (hM : Module.Flat R M) (q : PrimeSpectrum A) :
    Module.Flat.AtPrimeOver (R := R) (M := M) q := sorry

/-- Relative prime-local flatness is equivalent to flatness of the same localized module over
the original base ring. -/
@[stacks 00HT "relative prime-local flatness criterion"]
theorem atPrimeOver_iff (q : PrimeSpectrum A) :
    Module.Flat.AtPrimeOver (R := R) (M := M) q ↔
      Module.Flat R (LocalizedModule.AtPrime q.asIdeal M) := sorry

/-- Relative maximal-local flatness is equivalent to flatness of the same localized module over
the original base ring. -/
@[stacks 00HT "relative maximal-local flatness criterion"]
theorem atMaximalOver_iff (m : MaximalSpectrum A) :
    Module.Flat.AtMaximalOver (R := R) (M := M) m ↔
      Module.Flat R (LocalizedModule.AtPrime m.asIdeal M) := sorry

/-- Flatness of an `A`-module over `R` is detected at all local base rings
`Localization.AtPrime (q.asIdeal.under R)`. -/
@[stacks 00HT "flatness is local over contracted primes"]
theorem iff_forall_atPrimeOver :
    Module.Flat R M ↔
      ∀ q : PrimeSpectrum A, Module.Flat.AtPrimeOver (R := R) (M := M) q := sorry

/-- Flatness of an `A`-module over `R` is detected at all maximal local base
rings `Localization.AtPrime (m.asIdeal.under R)`. -/
@[stacks 00HT "flatness is local over contracted maximal ideals"]
theorem iff_forall_atMaximalOver :
    Module.Flat R M ↔
      ∀ m : MaximalSpectrum A, Module.Flat.AtMaximalOver (R := R) (M := M) m := sorry

end Relative

end Flat

end Module
