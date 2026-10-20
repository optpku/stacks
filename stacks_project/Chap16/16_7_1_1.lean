module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.Standard.Presentation.BaseRing

@[expose] public section

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/- Lemma 16.7.1.1 (tag 07CS): one finite presentation and one initial relation
segment satisfy both the Jacobian expansion and the base-ring tail condition. -/
@[stacks 07CS]
#check (Algebra.IsStrictlyStandard.Presentation.exists_baseRing_tail (R := R) (A := A) :
  ∀ {π : R}, Algebra.IsStrictlyStandard R (algebraMap R A π) →
    ∃ (n m : ℕ) (P : Algebra.Presentation R A (Fin n) (Fin m))
        (c : ℕ) (hcₘ : c ≤ m) (aI : Set.powersetCard (Fin n) c → A),
      algebraMap R A π = ∑ I : Set.powersetCard (Fin n) c,
          aI I * algebraMap P.Ring A
            (P.jacobianColumnMinor (Fin.castLEEmb hcₘ) I) ∧
        ∀ j : Fin (m - c),
          algebraMap R P.Ring π *
              P.relation (Fin.natAdd_castLEEmb (Nat.sub_le m c) j) ∈
            P.leadingRelationIdeal hcₘ + P.ker ^ 2)

/- The intrinsic tail condition is equivalent to the literal base-ring equation. -/
@[stacks 07CS]
#check (Algebra.Presentation.TailRelationCondition.iff_baseRing (R := R) (A := A) :
  ∀ {n m c : ℕ} (P : Algebra.Presentation R A (Fin n) (Fin m))
      (π : R) (hcₘ : c ≤ m),
    P.tailRelationCondition (algebraMap R A π) hcₘ ↔
      ∀ j : Fin (m - c),
        algebraMap R P.Ring π *
            P.relation (Fin.natAdd_castLEEmb (Nat.sub_le m c) j) ∈
          P.leadingRelationIdeal hcₘ + P.ker ^ 2)
