/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Beauville-Laszlo replacement modules

For a module that need not be glueable, the cycles of its canonical module
Cech sequence form a glueable replacement.  The canonical map to that
replacement becomes an isomorphism after base change and after localization,
and is already surjective over the base ring.

@stack 0BP9
-/

@[expose] public section

open CategoryTheory

universe u

noncomputable section

namespace LocalizedModule.Away.BeauvilleLaszlo

variable {R : Type u} [CommRing R]

/-- Remark 15.91.17 (1): the replacement of `M` is the cycles module of its
canonical Beauville-Laszlo module Cech sequence. -/
@[stacks 0BP9 "(1) Beauville-Laszlo replacement module"]
abbrev replacement (S : Type u) [CommRing S] [Algebra R S]
    (M : Type u) [AddCommGroup M] [Module R M] (f : R) : ModuleCat R :=
  (beauvilleLaszloModuleCechSequence S M f).cycles

/-- The canonical identification of the source of the module Cech sequence
with the original module. -/
@[stacks 0BP9 "source of the Beauville-Laszlo replacement map"]
noncomputable def replacementSourceIso
    (S : Type u) [CommRing S] [Algebra R S]
    (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    (beauvilleLaszloModuleCechSequence S M f).X₁ ≅ ModuleCat.of R M :=
  Iso.refl _

/-- The canonical map from a module to its Beauville-Laszlo replacement. -/
@[stacks 0BP9 "canonical map to the Beauville-Laszlo replacement"]
noncomputable abbrev replacementMap (S : Type u) [CommRing S] [Algebra R S]
    (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    M →ₗ[R] ↑(replacement S M f) :=
  ((replacementSourceIso S M f).inv ≫
    (beauvilleLaszloModuleCechSequence S M f).toCycles).hom

/-- Remark 15.91.17 (2): the cycles replacement is glueable for the same
Beauville-Laszlo glueing pair. -/
@[stacks 0BP9 "(2) the replacement module is glueable"]
theorem replacement_isGlueable (S : Type u) [CommRing S] [Algebra R S]
    (M : Type u) [AddCommGroup M] [Module R M] (f : R)
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R S) f) :
    (beauvilleLaszloModuleCechSequence S (replacement S M f) f).ShortExact := sorry

/-- Remark 15.91.17 (3): the canonical replacement map is bijective after
base change to the target ring. -/
@[stacks 0BP9 "(3) base-change bijectivity of the replacement map"]
theorem replacementMap_baseChange_bijective
    (S : Type u) [CommRing S] [Algebra R S]
    (M : Type u) [AddCommGroup M] [Module R M] (f : R)
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R S) f) :
    Function.Bijective ((replacementMap S M f).baseChange S) := sorry

/-- Remark 15.91.17 (4): the canonical replacement map is bijective after
localizing away from the distinguished element. -/
@[stacks 0BP9 "(4) localization bijectivity of the replacement map"]
theorem replacementMap_localizedAway_bijective
    (S : Type u) [CommRing S] [Algebra R S]
    (M : Type u) [AddCommGroup M] [Module R M] (f : R)
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R S) f) :
    Function.Bijective
      (LocalizedModule.map (Submonoid.powers f) (replacementMap S M f)) := sorry

/-- Remark 15.91.17 (5): the canonical map to the replacement module is
surjective. -/
@[stacks 0BP9 "(5) surjectivity of the replacement map"]
theorem replacementMap_surjective
    (S : Type u) [CommRing S] [Algebra R S]
    (M : Type u) [AddCommGroup M] [Module R M] (f : R)
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R S) f) :
    Function.Surjective (replacementMap S M f) := sorry

end LocalizedModule.Away.BeauvilleLaszlo
