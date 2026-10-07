module

public import ReasLib.RingTheory.Kaehler.NoetherDifferent

@[expose] public section

open scoped TensorProduct

universe u v

/- The reusable Noether-different data remains available through this compatibility module. -/
#check (KaehlerDifferential.noetherDifferent :
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B], Ideal B)

/- Its defining equation remains available through this compatibility module. -/
#check (KaehlerDifferential.noetherDifferent_eq_map :
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
    KaehlerDifferential.noetherDifferent A B =
      Ideal.map (Algebra.TensorProduct.lmul' A).toRingHom
        (KaehlerDifferential.ideal A B).annihilator)

/- Its membership characterization remains available through this compatibility module. -/
#check (KaehlerDifferential.mem_noetherDifferent :
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] (b : B),
    b ∈ KaehlerDifferential.noetherDifferent A B ↔
      ∃ ξ : B ⊗[A] B, ξ ∈ (KaehlerDifferential.ideal A B).annihilator ∧
        Algebra.TensorProduct.lmul' A ξ = b)
