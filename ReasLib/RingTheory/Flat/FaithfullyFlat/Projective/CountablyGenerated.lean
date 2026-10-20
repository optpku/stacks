/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Finiteness.Projective.CountablyGenerated
public import ReasLib.RingTheory.Flat.FaithfullyFlat.CountablyGenerated
import Mathlib.Tactic.CrossRefAttribute
import ReasLib.RingTheory.Flat.Projective
import ReasLib.RingTheory.Flatness.MittagLeffler.BaseChange
import ReasLib.RingTheory.Flatness.MittagLeffler.Projective

/-!
# Faithfully flat descent of countably generated projective modules

This leaf records faithfully flat descent for the canonical predicate of a countably generated
projective module.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Module.CountablyGeneratedProjective

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M]

/-- Lemma 10.95.3 (05A6): countably generated projectivity descends along a faithfully flat
scalar extension. -/
@[stacks 05A6]
theorem of_baseChange [Module.FaithfullyFlat R S]
    (hM : Module.CountablyGeneratedProjective S (S ⊗[R] M)) :
    Module.CountablyGeneratedProjective R M := sorry

/-- Countably generated projectivity is invariant under faithfully flat scalar extension. -/
@[stacks 05A6 "faithfully flat base change"]
theorem iff_baseChange [Module.FaithfullyFlat R S] :
    Module.CountablyGeneratedProjective R M ↔
      Module.CountablyGeneratedProjective S (S ⊗[R] M) := sorry

end Module.CountablyGeneratedProjective
