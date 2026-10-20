module

public import ReasLib.RingTheory.Topology.FiniteType.Reduction.Taut
import StacksCheckRecall

/-!
# Taut topologically finite type maps are finite type on reductions
-/

@[expose] public section

universe u

open TopologicalRing

/- Lemma 88.12.4: Let `φ : A →+* B` be an arrow of `WAdm^count`. If `φ` is taut
and topologically of finite type, then `φ` satisfies the finite type on
reduction condition of Lemma 88.12.1. -/
@[stacks 0GC5] #check (RingHom.IsFiniteTypeOnReduction.of_isTaut_topologicallyOfFiniteType :
    ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
    {φ : A →+* B}, Continuous φ → φ.IsTaut → φ.TopologicallyOfFiniteType →
    φ.IsFiniteTypeOnReduction)
