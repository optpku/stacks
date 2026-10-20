module

public import ReasLib.RingTheory.AdicCompletion.RigSmooth
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 88.4.1: let `A` be a Noetherian ring and let `I ⊆ A` be an ideal.
Let `B` be an object of `C'` (`Algebra.TopologicallyFiniteType I B`: `B` is
`I`-adically complete and `B ⧸ I B` is of finite type over `A ⧸ I`). We say `B`
is rig-smooth over `(A, I)` if there exists an integer `c ≥ 0` such that
`I ^ c` annihilates `Ext¹_B(NL_{B/A}^∧, N)` for every `B`-module `N`. -/
@[stacks 0GAI] #check (Algebra.RigSmooth :
  ∀ {A : Type u} [CommRing A] (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B], Prop)
