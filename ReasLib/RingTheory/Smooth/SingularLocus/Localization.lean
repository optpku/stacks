/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.RingTheory.RingHom.Smooth
public import ReasLib.RingTheory.Smooth.AtPrime.Locality
public import ReasLib.RingTheory.Smooth.SingularLocus

@[expose] public section

/-!
# Singular ideals and localization

The singular ideal detects the principal localizations on which an algebra
is smooth.  These statements use the Stacks-style `SmoothAtPrime`, so no
finite-presentation assumption is needed.

@stack 07C5
-/

universe u v

namespace Algebra

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A]

/-- A principal open consists of smooth points exactly when its localization
is smooth. -/
@[stacks 07C5 "principal-open singular-locus criterion"]
theorem basicOpen_subset_smoothAtPrime_iff_smooth {a : A} :
    (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) ⊆
        {q | SmoothAtPrime R A q} ↔
      Smooth R (Localization.Away a) := sorry

namespace SingularIdeal

/-- Membership in the singular ideal detects smoothness after localization. -/
@[stacks 07C5 "singular-ideal localization criterion"]
theorem mem_iff_smoothAway {a : A} :
    a ∈ singularIdeal R A ↔ Smooth R (Localization.Away a) := sorry

/-- A base element belongs to the singular ideal exactly when the induced
map between the corresponding principal localizations is smooth. -/
@[stacks 07C5 "base-element singular-ideal localization criterion"]
theorem algebraMap_mem_iff_awayMap_smooth {r : R} :
    algebraMap R A r ∈ singularIdeal R A ↔
      (Localization.awayMap (algebraMap R A) r).Smooth := sorry

/-- The singular ideal is the unit ideal exactly when the algebra is smooth. -/
@[stacks 07C5 "unit singular ideal criterion"]
theorem eq_top_iff_smooth :
    singularIdeal R A = ⊤ ↔ Smooth R A := sorry

end SingularIdeal

end Algebra
