module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.RingTheory.RingHom.Perfect.Basic

/-!
# Polynomial presentation criteria for perfect ring maps

This leaf exposes the presentation criterion in the ordinary algebra-map
notation used by most algebraic applications.

@stack 068Y
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace RingHom

/-- A ring map has a perfect finite polynomial presentation when some surjective finite
polynomial presentation makes the target a perfect module over the polynomial ring. -/
@[stacks 068Y "perfect polynomial presentation predicate"]
def HasPerfectPolynomialPresentation
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B) : Prop :=
  let _ : Algebra A B := f.toAlgebra
  ∃ (n : ℕ) (α : MvPolynomial (Fin n) A →ₐ[A] B),
    Function.Surjective α ∧
      let _ : Module (MvPolynomial (Fin n) A) B := Module.compHom B α.toRingHom
      (ModuleCat.of (MvPolynomial (Fin n) A) B).IsPerfect

/-- Lemma 15.83.2: a ring map is perfect exactly when it admits a perfect finite polynomial
presentation. -/
@[stacks 068Y "perfect polynomial presentation"]
theorem isPerfectRingMap_iff_hasPerfectPolynomialPresentation
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B) :
    f.IsPerfectRingMap ↔ f.HasPerfectPolynomialPresentation := sorry
/- Proof strategy: choose a finite polynomial presentation from pseudo-coherence; combine relative
pseudo-coherence with finite Tor dimension using the perfect-complex criterion. Conversely, a
perfect restricted target module is pseudo-coherent and has finite Tor dimension over `A`, so
`RingHom.isPerfectRingMap_iff` applies. -/

namespace IsPerfectRingMap

/-- A perfect ring map admits a finite polynomial presentation whose restricted target module is
perfect. -/
theorem exists_perfectPolynomialPresentation
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] {f : A →+* B}
    (h : f.IsPerfectRingMap) :
    let _ : Algebra A B := f.toAlgebra
    ∃ (n : ℕ) (α : MvPolynomial (Fin n) A →ₐ[A] B), Function.Surjective α ∧
      let _ : Module (MvPolynomial (Fin n) A) B := Module.compHom B α.toRingHom
      (ModuleCat.of (MvPolynomial (Fin n) A) B).IsPerfect := sorry
/- Proof strategy: take the forward implication of
`isPerfectRingMap_iff_hasPerfectPolynomialPresentation`, unfold the presentation predicate, and
normalize the algebra structure induced by `f`. -/

end IsPerfectRingMap

end RingHom

namespace Algebra

/-- A structure map is perfect exactly when some surjective finite polynomial presentation makes
the target a perfect module over its polynomial source. -/
theorem isPerfectRingMap_iff_hasPerfectPolynomialPresentation
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] :
    (algebraMap A B).IsPerfectRingMap ↔
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) A →ₐ[A] B), Function.Surjective α ∧
        let _ : Module (MvPolynomial (Fin n) A) B := Module.compHom B α.toRingHom
        (ModuleCat.of (MvPolynomial (Fin n) A) B).IsPerfect := sorry
/- Proof strategy: specialize the intrinsic RingHom criterion to `algebraMap A B` and unfold
`RingHom.HasPerfectPolynomialPresentation`; the induced algebra is definitionally the ambient
algebra after the standard algebra-map extensionality bridge. -/

/-- A perfect restricted target module on a surjective finite polynomial presentation makes the
structure map perfect. -/
theorem isPerfectRingMap_of_hasPerfectPolynomialPresentation
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    {n : ℕ} (α : MvPolynomial (Fin n) A →ₐ[A] B) (h_surjective : Function.Surjective α)
    (h_perfect :
      let _ : Module (MvPolynomial (Fin n) A) B := Module.compHom B α.toRingHom
      (ModuleCat.of (MvPolynomial (Fin n) A) B).IsPerfect) :
    (algebraMap A B).IsPerfectRingMap := sorry
/- Proof strategy: package `n`, `α`, `h_surjective`, and `h_perfect` as a
`HasPerfectPolynomialPresentation` witness, then use the reverse implication of the algebra-map
presentation criterion. -/

end Algebra
