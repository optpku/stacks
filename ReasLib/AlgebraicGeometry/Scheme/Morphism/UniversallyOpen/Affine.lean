module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

@[expose] public section

open scoped BigOperators

universe u

namespace AlgebraicGeometry.UniversallyOpen

/-- If a finite family `b : Fin d → B` spans an `A`-algebra `B` as an `A`-module, then
`Spec B ⟶ Spec A` is universally open exactly when the image of the basic open defined by
the linear form `∑ i, X i * C (b i)` is open in `Spec (MvPolynomial (Fin d) A)`. -/
theorem specMap_iff_isOpen_image_linearForm
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {d : ℕ} (b : Fin d → B) (hgen : Submodule.span A (Set.range b) = ⊤) :
    let h : MvPolynomial (Fin d) B :=
      ∑ i, MvPolynomial.X i * MvPolynomial.C (b i)
    AlgebraicGeometry.UniversallyOpen
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A B))) ↔
      IsOpen (PrimeSpectrum.comap (MvPolynomial.map (algebraMap A B)) ''
        (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum (MvPolynomial (Fin d) B)))) := sorry

end AlgebraicGeometry.UniversallyOpen
