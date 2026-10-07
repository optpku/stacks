module

public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Flatness.Nilpotent

/-!
# Flatness over Artinian Bases

This leaf owns the Artinian specialization of the nilpotent flatness criterion.  The source
presentation is retained as the canonical tensor-product statement, while the Jacobson-radical
argument remains proof debt on the proposition-valued theorem only.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Module.Flat.Artinian

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [Algebra R S] [IsArtinianRing R]
variable {M : Type w} [AddCommGroup M] [Module R M]

/-- Lemma 10.101.7 (Stacks `051L`): over an Artinian base, an injective algebra map whose tensor
base change of an `R`-module is flat forces the original module to be flat. -/
@[stacks 051L]
theorem of_injective_algebraMap
    (hinj : Function.Injective (algebraMap R S))
    (hflat : Module.Flat S (S ⊗[R] M)) :
    Module.Flat R M := sorry

end Module.Flat.Artinian
