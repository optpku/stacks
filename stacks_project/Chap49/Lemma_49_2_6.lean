/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing.Transitivity
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped Algebra.DualModule Algebra.RelativeDual TensorProduct TensorProduct.Right

universe u

/- Lemma 49.2.6: for quasi-finite homomorphisms of Noetherian rings `A → B → C`,
the finite-open models define the canonical map
`ω_{B/A} ⊗[B] ω_{C/B} → ω_{C/A}`. Here `B ⊗[B'] C'` is the finite `B`-model
of `C`; the source is canonically normalized by tensor reassociation and flat
dual base change before composing relative duals. -/
@[stacks 0BT4] #check
  (@Algebra.RelativeDualizingModule.transitivityMapOf :
    ∀ (A B B' C C' : Type u)
      [CommRing A] [CommRing B] [CommRing B'] [CommRing C] [CommRing C']
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
      [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [Algebra B' C] [IsScalarTower B' B C]
      [Algebra B' C'] [Algebra A C'] [IsScalarTower A B' C']
      [Algebra C' C] [IsScalarTower B' C' C] [IsScalarTower A C' C]
      (h_quasiFiniteAB : Algebra.FiniteType.QuasiFinite A B)
      (h_quasiFiniteBC : Algebra.FiniteType.QuasiFinite B C)
      [Module.Finite A B'] [Module.Finite B' C'] [Module.Finite A C']
      (h_openB : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
      (h_openC : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap C' C)))),
      (Algebra.RelativeDualizingModule.of A B' B h_quasiFiniteAB h_openB ⊗[B]
          Algebra.RelativeDualizingModule.of B (B ⊗[B'] C') C h_quasiFiniteBC
            (Algebra.RelativeDual.baseChange_isOpenImmersion B' B C' C h_openC)) →ₗ[C]
        Algebra.RelativeDualizingModule.of A C' C
          (h_quasiFiniteAB.comp h_quasiFiniteBC) h_openC)

/- On normalized pure tensors, the map is dual composition followed by scalar extension. -/
#check
  (@Algebra.RelativeDualizingModule.transitivityMapOf_apply_normalizationToSource_tmul :
    ∀ (A B B' C C' : Type u)
      [CommRing A] [CommRing B] [CommRing B'] [CommRing C] [CommRing C']
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
      [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [Algebra B' C] [IsScalarTower B' B C]
      [Algebra B' C'] [Algebra A C'] [IsScalarTower A B' C']
      [Algebra C' C] [IsScalarTower B' C' C] [IsScalarTower A C' C]
      (h_quasiFiniteAB : Algebra.FiniteType.QuasiFinite A B)
      (h_quasiFiniteBC : Algebra.FiniteType.QuasiFinite B C)
      [Module.Finite A B'] [Module.Finite B' C'] [Module.Finite A C']
      (h_openB : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
      (h_openC : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap C' C))))
      (c : C) (g : Module.Dual B' C') (f : Module.Dual A B'),
      Algebra.RelativeDualizingModule.transitivityMapOf A B B' C C'
          h_quasiFiniteAB h_quasiFiniteBC h_openB h_openC
          (Algebra.RelativeDual.normalizationToSource A B B' C C' h_quasiFiniteAB
            h_quasiFiniteBC h_openB h_openC (c ⊗ₜ (g ⊗ₜ f))) =
        Algebra.RelativeDual.comp A B' C' g f ⊗ₜ[C'] c)
