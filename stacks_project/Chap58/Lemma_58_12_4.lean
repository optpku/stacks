module

public import ReasLib.RingTheory.Invariant.FixedPoints.Etale
import StacksCheckRecall

@[expose] public section

universe u v

namespace FixedPoints

/- Lemma 58.12.4 -/
@[stacks 0BST] #check (FixedPoints.etaleAt_inertia :
    ∀ {R : Type u} {G : Type v}, [CommRing R] → [Group G] → [Finite G] →
      [MulSemiringAction G R] → (q : Ideal R) → [q.IsPrime] →
      -- Local instance justification (defeq pin): Localization.Away must use subalgebraAlgebraOfLe as the full-to-inertia fixed-subalgebra inclusion.
      (letI : Algebra (FixedPoints.subalgebra ℤ R (⊤ : Subgroup G))
          (FixedPoints.subalgebra ℤ R (q.inertia G)) :=
        FixedPoints.subalgebraAlgebraOfLe (le_top : q.inertia G ≤ (⊤ : Subgroup G));
        ∃ element : FixedPoints.subalgebra ℤ R (q.inertia G),
          element ∉ q.under (FixedPoints.subalgebra ℤ R (q.inertia G)) ∧
          Algebra.Etale (FixedPoints.subalgebra ℤ R (⊤ : Subgroup G))
            (Localization.Away element)))

end FixedPoints
