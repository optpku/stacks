/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u

open MvPolynomial

namespace Algebra

/-- The naive pre-submersive presentation of the square quotient
`R[x₁,…,xₙ] ⧸ (f₁,…,fₙ)`. -/
noncomputable def naiveSquarePresentation {R : Type u} [CommRing R] (n : ℕ)
    (f : Fin n → MvPolynomial (Fin n) R) :
    PreSubmersivePresentation R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
      (Fin n) (Fin n) :=
  PreSubmersivePresentation.naive (fun i : Fin n ↦ i) Function.injective_id

/-- The Jacobian determinant of the square presentation `R[x₁,…,xₙ] ⧸ (f₁,…,fₙ)`,
as an element of the presented algebra. -/
noncomputable def squareJacobian {R : Type u} [CommRing R] (n : ℕ)
    (f : Fin n → MvPolynomial (Fin n) R) :
    MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f) :=
  (naiveSquarePresentation n f).jacobian

/-- The Jacobian of a square presentation is the class of `det (∂fᵢ / ∂xⱼ)`. -/
theorem squareJacobian_eq_det {R : Type u} [CommRing R] (n : ℕ)
    (f : Fin n → MvPolynomial (Fin n) R) :
    squareJacobian n f =
      Ideal.Quotient.mk (Ideal.span (Set.range f))
        (Matrix.det fun i j : Fin n ↦ pderiv j (f i)) :=
  sorry

/-- The mathlib submersive presentation of `R[x₁,…,xₙ] ⧸ (f₁,…,fₙ)` when the
Jacobian is a unit. -/
noncomputable def toSubmersive {R : Type u} [CommRing R] (n : ℕ)
    (f : Fin n → MvPolynomial (Fin n) R) (hjac : IsUnit (squareJacobian n f)) :
    SubmersivePresentation R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
      (Fin n) (Fin n) where
  toPreSubmersivePresentation := naiveSquarePresentation n f
  jacobian_isUnit := hjac

/-- A square presentation has relative dimension `0`. -/
theorem toSubmersive_dimension {R : Type u} [CommRing R] (n : ℕ)
    (f : Fin n → MvPolynomial (Fin n) R) (hjac : IsUnit (squareJacobian n f)) :
    (toSubmersive n f hjac).dimension = 0 :=
  sorry

/-- A square presentation with invertible Jacobian is standard smooth of relative
dimension `0`. -/
instance instIsStandardSmoothOfRelativeDimension_of_isUnit_jacobian
    {R : Type u} [CommRing R] (n : ℕ) (f : Fin n → MvPolynomial (Fin n) R)
    (hjac : IsUnit (squareJacobian n f)) :
    let _ := hjac
    IsStandardSmoothOfRelativeDimension 0 R
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)) :=
  sorry

/-- For equally many generators and relations, the Jacobian is a unit if and only
if `Ω[A⁄R]` is a subsingleton. -/
theorem isUnit_squareJacobian_iff_subsingleton_kaehlerDifferential
    {R : Type u} [CommRing R] (n : ℕ) (f : Fin n → MvPolynomial (Fin n) R) :
    IsUnit (squareJacobian n f) ↔
      Subsingleton Ω[(MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))⁄R] :=
  sorry

namespace FormallyEtale

/-- Exercise 111.50.3: if `A = R[x₁,…,xₙ] ⧸ (f₁,…,fₙ)` has invertible Jacobian
determinant, then every `R`-algebra map `φ : A → B` lifts uniquely along a
surjection `π : B' → B` whose kernel has square zero. -/
@[stacks 02FE]
theorem existsUnique_lift_of_isUnit_jacobian
    {R B' B : Type u} [CommRing R] [CommRing B'] [CommRing B]
    [Algebra R B'] [Algebra R B] (n : ℕ) (f : Fin n → MvPolynomial (Fin n) R)
    (hjac : IsUnit (squareJacobian n f)) (π : B' →ₐ[R] B)
    (hπ : Function.Surjective π) (hker : (RingHom.ker π) ^ 2 = ⊥)
    (φ : (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)) →ₐ[R] B) :
    ∃! φ' : (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)) →ₐ[R] B',
      π.comp φ' = φ :=
  sorry

end FormallyEtale

end Algebra
