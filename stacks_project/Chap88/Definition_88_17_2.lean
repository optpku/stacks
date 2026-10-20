module

public import ReasLib.RingTheory.AdicCompletion.RigSmooth
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 88.17.2: let `φ : A →+* B` be a continuous ring homomorphism
between adic Noetherian topological rings, i.e., `φ` is an arrow of
`WAdm^{Noeth}`. We say `φ` is rig-smooth if the equivalent conditions of
Lemma 88.17.1 hold. -/
@[stacks 0GCJ] #check (RingHom.RigSmooth :
  ∀ {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B], (A →+* B) → Prop)
