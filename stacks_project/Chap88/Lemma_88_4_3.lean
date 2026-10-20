module

public import ReasLib.RingTheory.AdicCompletion.RigSmooth.FiniteType
import StacksCheckRecall

/-!
# Finite-type smoothness away from V(I) versus rig-smoothness of the completion

Lemma 88.4.3 compares smoothness of Spec B → Spec A over Spec A \ V(I)
with rig-smoothness of the I-adic completion B^∧.
-/

@[expose] public section

universe u

/- Lemma 88.4.3. Smoothness over Spec A \ V(I) implies rig-smoothness of
the completion, and the converse holds after localization at an element of 1 + IB. -/
@[stacks 0GAK] #check (Algebra.RigSmooth.of_isSmoothOverComplement :
  ∀ {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B]
    [Algebra A B] [Algebra.FiniteType A B] (I : Ideal A),
    Algebra.IsSmoothOverComplement I B →
      Algebra.RigSmooth I (AdicCompletion (I.map (algebraMap A B)) B))

#check (Algebra.RigSmooth.exists_mem_oneAdd_isSmoothOverComplement :
  ∀ {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B]
    [Algebra A B] [Algebra.FiniteType A B] (I : Ideal A)
    [Algebra.RigSmooth I (AdicCompletion (I.map (algebraMap A B)) B)],
    ∃ g : B, g ∈ (I.map (algebraMap A B)).oneAdd ∧
      Algebra.IsSmoothOverComplement I (Localization.Away g))
