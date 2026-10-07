module

import StacksCheckRecall
public import ReasLib.Algebra.Module.RelativeDualizing.NoetherPairing.Bijective

@[expose] public section

open AlgebraicGeometry

universe u v

namespace Algebra.RelativeDualizingModule

/- Lemma 49.6.6: for a flat quasi-finite homomorphism `A → B` of Noetherian
rings, the transpose of the Noether pairing is a bijection from the annihilator
`J` of the diagonal ideal to the `B`-linear dual of `ω_{B/A}`. -/
@[stacks 0BVS] #check
  (Algebra.RelativeDualizingModule.noetherPairing_flip_bijective_of_flat :
    ∀ (A : Type u) (B' B : Type v),
      [CommRing A] → [CommRing B'] → [CommRing B] →
      [IsNoetherianRing A] → [IsNoetherianRing B] →
      [Algebra A B'] → [Algebra B' B] → [Algebra A B] →
      [IsScalarTower A B' B] → [Module.Flat A B] →
      (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) → [Module.Finite A B'] →
      (h_open : IsOpenImmersion
        (Spec.map (CommRingCat.ofHom (algebraMap B' B)))) →
      Function.Bijective
        ((noetherPairing A B' B h_quasiFinite h_open).flip :
          (KaehlerDifferential.ideal A B).annihilator →ₗ[B]
            Module.Dual B
              (RelativeDualizingModule.of A B' B h_quasiFinite h_open)))

end Algebra.RelativeDualizingModule
