/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.39.1

@stack 00HB
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section module_flat

variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/- Definition 10.39.1 (1): an `R`-module `M` is flat when tensoring with `M` preserves exact
sequences; the canonical mathlib predicate for this notion is `Module.Flat R M`. -/
@[stacks 00HB "module flatness"]
#check @Module.Flat

/- Companion recall: the textbook exact-sequence formulation of flatness is the canonical
equivalence `Module.Flat.iff_lTensor_preserves_shortComplex_exact`. -/
@[stacks 00HB "module flatness criterion"]
#check @Module.Flat.iff_lTensor_preserves_shortComplex_exact

/- Definition 10.39.1 (2): an `R`-module `M` is faithfully flat when tensoring with `M`
preserves and reflects exact sequences; the canonical mathlib predicate for this notion is
`Module.FaithfullyFlat R M`. -/
@[stacks 00HB "module faithful flatness"]
#check @Module.FaithfullyFlat

/- Companion recall: the textbook exact-sequence characterization of faithful flatness is the
canonical equivalence `Module.FaithfullyFlat.iff_exact_iff_lTensor_exact`. -/
@[stacks 00HB "faithful flatness criterion"]
#check @Module.FaithfullyFlat.iff_exact_iff_lTensor_exact

end module_flat

section ring_hom_flat

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable (f : R →+* S)

/- Definition 10.39.1 (3): a ring map `f : R →+* S` is flat when `S` is flat as an `R`-module;
the canonical mathlib predicate for this notion is `RingHom.Flat f`. -/
@[stacks 00HB "ring-hom flatness"]
#check @RingHom.Flat

/- Definition 10.39.1 (4): a ring map `f : R →+* S` is faithfully flat when `S` is faithfully flat
as an `R`-module; the canonical mathlib predicate for this notion is `RingHom.FaithfullyFlat f`. -/
@[stacks 00HB "ring-hom faithful flatness"]
#check @RingHom.FaithfullyFlat

end ring_hom_flat

section algebra_flat

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Companion recall for Definition 10.39.1 (3): for the canonical algebra map, the textbook
wording "flat as an `R`-module" is exactly `RingHom.flat_algebraMap_iff`. -/
@[stacks 00HB "algebra-map flatness"]
#check @RingHom.flat_algebraMap_iff

/- Companion recall for Definition 10.39.1 (4): for the canonical algebra map, the textbook
wording "faithfully flat as an `R`-module" is exactly
`RingHom.faithfullyFlat_algebraMap_iff`. -/
@[stacks 00HB "algebra-map faithful flatness"]
#check @RingHom.faithfullyFlat_algebraMap_iff

end algebra_flat
