module

public import ReasLib.Algebra.IndEtaleEnvelope.Cardinality

@[expose] public section

universe u

open scoped Cardinal

#check
  (Algebra.IndEtaleEnvelope.mk_presentation_le :
    ∀ (A : Type u) [CommRing A] {κ : Cardinal.{u}}, ℵ₀ ≤ κ → #A ≤ κ →
      #(Algebra.IndEtaleEnvelope.Presentation A) ≤ κ)
#check
  (Algebra.IndEtaleEnvelope.mk_index_le :
    ∀ (A : Type u) [CommRing A] {κ : Cardinal.{u}}, ℵ₀ ≤ κ → #A ≤ κ →
      #(Algebra.IndEtaleEnvelope.Index A) ≤ κ)
#check
  (Algebra.IndEtaleEnvelope.mk_stage_le :
    ∀ (A : Type u) [CommRing A] {κ : Cardinal.{u}}, ℵ₀ ≤ κ → #A ≤ κ →
      (E : Algebra.IndEtaleEnvelope.Index A) →
        #(Algebra.IndEtaleEnvelope.stage E) ≤ κ)
#check
  (Algebra.IndEtaleEnvelope.mk_le_max :
    ∀ (A : Type u) [CommRing A],
      #(Algebra.IndEtaleEnvelope A) ≤ #A ⊔ ℵ₀)
#check
  (Algebra.IndEtaleEnvelope.mk_iterate_le :
    ∀ (A : Type u) [CommRing A] {κ : Cardinal.{u}}, ℵ₀ ≤ κ → #A ≤ κ →
      (n : ℕ) → #(Algebra.IndEtaleEnvelope.iterate A n) ≤ κ)
#check
  (Algebra.IndEtaleEnvelope.mk_iteration_le_max :
    ∀ (A : Type u) [CommRing A],
      #(Algebra.IndEtaleEnvelope.Iteration A) ≤ #A ⊔ ℵ₀)
