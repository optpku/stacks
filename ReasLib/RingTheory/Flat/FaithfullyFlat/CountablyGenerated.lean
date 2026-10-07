module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import ReasLib.Algebra.Module.CountablyGenerated.BaseChange
import Mathlib.Tactic.CrossRefAttribute

/-!
# Faithfully flat descent of countable generation

Countable generation is preserved by arbitrary scalar extension and reflected by faithfully flat
scalar extension. The preservation theorem stays in the algebraic base-change leaf.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Module.CountablyGenerated

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

/-- Lemma 10.95.2 (0GVD): countable generation descends along a faithfully flat scalar
extension. -/
@[stacks 0GVD]
theorem of_baseChange [Module.FaithfullyFlat R S]
    (hM : Module.CountablyGenerated S (S ⊗[R] M)) :
    Module.CountablyGenerated R M := sorry

/-- Countable generation is invariant under faithfully flat scalar extension. -/
@[stacks 0GVD "faithfully flat base change"]
theorem iff_baseChange [Module.FaithfullyFlat R S] :
    Module.CountablyGenerated R M ↔
      Module.CountablyGenerated S (S ⊗[R] M) := sorry

end Module.CountablyGenerated
