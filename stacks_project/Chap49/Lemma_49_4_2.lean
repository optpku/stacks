module

import ReasLib.Algebra.Module.RelativeDualizing.TraceElement
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 49.4.2: for a flat quasi-finite map of Noetherian rings `A → B`, any two
trace elements in `ω_{B/A}` are equal. -/
@[stacks 0BT7] #check
  (Algebra.RelativeDualizingModule.TraceElement.IsUniversal.eq :
    ∀ {A B' B : Type u} [CommRing A] [CommRing B'] [CommRing B]
      [IsNoetherianRing A] [IsNoetherianRing B]
      [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
      [Module.Flat A B] {h_quasiFinite : Algebra.FiniteType.QuasiFinite A B}
      [Module.Finite A B']
      {h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))}
      {τ₁ τ₂ : Algebra.RelativeDualizingModule.of A B' B h_quasiFinite h_open},
      Algebra.RelativeDualizingModule.TraceElement.IsUniversal
        A B' B h_quasiFinite h_open τ₁ →
      Algebra.RelativeDualizingModule.TraceElement.IsUniversal
        A B' B h_quasiFinite h_open τ₂ →
      τ₁ = τ₂)
