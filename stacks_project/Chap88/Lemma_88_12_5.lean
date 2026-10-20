module

public import ReasLib.RingTheory.Topology.FiniteType.Reduction.Noetherian
import StacksCheckRecall

/-!
# Finite type on reductions implies topological finite type for Noetherian adic rings
-/

@[expose] public section

universe u

open TopologicalRing

/- Lemma 88.12.5: Let `φ : A →+* B` be an arrow of `WAdm^Noeth` satisfying
the condition of Lemma 88.12.1. Then `φ` is topologically of finite type. -/
@[stacks 0GC6] #check (RingHom.topologicallyOfFiniteType_of_isFiniteTypeOnReduction :
    ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
    (φ : A →+* B), Continuous φ → φ.IsFiniteTypeOnReduction →
      φ.TopologicallyOfFiniteType)
