module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerCharacteristic
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower

/-!
# Hilbert polynomials of invertible modules

The Hilbert polynomial of an invertible module on a scheme proper over a field
is specified by the Euler characteristics of all its integral tensor powers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The Hilbert polynomial of an invertible module `L` on a scheme proper over a
field is the function `t ↦ χ(X, L^{⊗ t})`. -/
def HasHilbertPolynomial {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsLocallyNoetherian X]
    (L : X.Modules) [Scheme.Modules.Invertible L] (P : ℤ → ℤ) : Prop :=
  ∀ t : ℤ, Scheme.Hom.eulerCharacteristic f (Scheme.Modules.tensorPowerInt L t) = P t

/-- Having Hilbert polynomial `P` means `χ(X, L^{⊗ t}) = P t` for every integer
`t`. -/
theorem hasHilbertPolynomial_iff {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsLocallyNoetherian X]
    (L : X.Modules) [Scheme.Modules.Invertible L] (P : ℤ → ℤ) :
    HasHilbertPolynomial f L P ↔
      ∀ t : ℤ,
        Scheme.Hom.eulerCharacteristic f (Scheme.Modules.tensorPowerInt L t) = P t :=
  sorry

end AlgebraicGeometry.Scheme.Hom
