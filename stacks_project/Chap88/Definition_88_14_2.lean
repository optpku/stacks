module

public import ReasLib.RingTheory.Ideal.RigClosed
import StacksCheckRecall

@[expose] public section

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]

/- Definition 88.14.2: let `A` be a Noetherian adic topological ring. Let `q ⊂ A`
be a prime ideal. We say `q` is rig-closed if the equivalent conditions of
Lemma 88.14.1 are satisfied. -/
@[stacks 0GG9] #check (Ideal.IsRigClosed : Ideal A → Prop)
