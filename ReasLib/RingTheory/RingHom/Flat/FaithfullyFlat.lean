/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Flatness Detected by a Faithfully Flat Module

This leaf places the flat-map descent criterion with `RingHom.Flat`, the
property it proves. The auxiliary module is necessarily explicit because it
does not occur in the resulting ring map.
-/

@[expose] public section

universe u v w

namespace RingHom.Flat

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Stacks `039V`: if an `S`-module is flat over `R` and faithfully flat over
`S`, then the algebra map from `R` to `S` is flat. -/
@[stacks 039V]
theorem of_flat_of_faithfullyFlat (M : Type w) [AddCommGroup M] [Module S M]
    [Module.Flat R (RestrictScalars R S M)] [Module.FaithfullyFlat S M] :
    (algebraMap R S).Flat := sorry

end RingHom.Flat
