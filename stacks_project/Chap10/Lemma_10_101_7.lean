module

public import ReasLib.RingTheory.Flatness.Artinian
import StacksCheckRecall

/-!
# Flatness descent from an injective extension of an Artinian ring

@stack 051L
-/

@[expose] public section

open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [Algebra R S] [IsArtinianRing R]
variable {M : Type w} [AddCommGroup M] [Module R M]

/- Lemma 10.101.7: the Artinian injective-base-change flatness criterion is owned by
`Module.Flat.Artinian.of_injective_algebraMap`. -/
@[stacks 051L]
#check (Module.Flat.Artinian.of_injective_algebraMap :
  Function.Injective (algebraMap R S) →
    Module.Flat S (S ⊗[R] M) → Module.Flat R M)

end
