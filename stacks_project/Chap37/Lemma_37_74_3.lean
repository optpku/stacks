/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversallyOpen.Affine
import StacksCheckRecall

@[expose] public section

open scoped BigOperators

universe u

/- Lemma 37.74.3: if `b : Fin d → B` generates the `A`-module `B`, then
`Spec B ⟶ Spec A` is universally open exactly when the image of the basic open defined by
the linear form `∑ i, X i * C (b i)` is open in `Spec (MvPolynomial (Fin d) A)`. -/
@[stacks 0F33] #check
  (AlgebraicGeometry.UniversallyOpen.specMap_iff_isOpen_image_linearForm :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
      {d : ℕ} (b : Fin d → B), Submodule.span A (Set.range b) = ⊤ →
        let h : MvPolynomial (Fin d) B :=
          ∑ i, MvPolynomial.X i * MvPolynomial.C (b i)
        AlgebraicGeometry.UniversallyOpen
            (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A B))) ↔
          IsOpen (PrimeSpectrum.comap (MvPolynomial.map (algebraMap A B)) ''
            (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum (MvPolynomial (Fin d) B)))))
