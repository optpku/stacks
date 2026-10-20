module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import ReasLib.AlgebraicGeometry.BivariantClass.Additive

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.Nonnegative.Rational

variable {S : Scheme.{u}} (δ : S → ℤ) [UniversallyCatenary S] [IsDimensionFunction δ]
variable {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]

/-- The rationalization of a nonnegative homogeneous bivariant degree, with the
integral class as the first tensor factor. -/
abbrev Degree (f : X ⟶ Y) (p : ℕ) : Type (u + 1) :=
  @TensorProduct ℤ inferInstance (BivariantClass δ f (p : ℤ)) ℚ
    (pointwiseAddCommGroup δ f (p : ℤ)).toAddCommMonoid inferInstance
    (@AddCommGroup.toIntModule _ (pointwiseAddCommGroup δ f (p : ℤ))) inferInstance

/-- A rational homogeneous degree is the integral-first tensor product over `ℤ`. -/
theorem degree_def (f : X ⟶ Y) (p : ℕ) :
    Degree δ f p =
      @TensorProduct ℤ inferInstance (BivariantClass δ f (p : ℤ)) ℚ
        (pointwiseAddCommGroup δ f (p : ℤ)).toAddCommMonoid inferInstance
        (@AddCommGroup.toIntModule _ (pointwiseAddCommGroup δ f (p : ℤ))) inferInstance := rfl

/-- The pure tensor of an integral homogeneous class and a rational coefficient. -/
def tensor (f : X ⟶ Y) (p : ℕ) (c : BivariantClass δ f (p : ℤ)) (q : ℚ) :
    Degree δ f p :=
  @TensorProduct.tmul ℤ inferInstance (BivariantClass δ f (p : ℤ)) ℚ
    (pointwiseAddCommGroup δ f (p : ℤ)).toAddCommMonoid inferInstance
    (@AddCommGroup.toIntModule _ (pointwiseAddCommGroup δ f (p : ℤ))) inferInstance c q

/-- The rational tensor is computed using the pointwise additive structure on classes. -/
theorem tensor_def (f : X ⟶ Y) (p : ℕ) (c : BivariantClass δ f (p : ℤ)) (q : ℚ) :
    tensor δ f p c q =
      @TensorProduct.tmul ℤ inferInstance (BivariantClass δ f (p : ℤ)) ℚ
        (pointwiseAddCommGroup δ f (p : ℤ)).toAddCommMonoid inferInstance
        (@AddCommGroup.toIntModule _ (pointwiseAddCommGroup δ f (p : ℤ))) inferInstance c q := rfl

/-- The completed product of all rationalized nonnegative bivariant degrees. -/
abbrev Completion (f : X ⟶ Y) : Type (u + 1) :=
  ∀ p : ℕ, Degree δ f p

/-- The rational completion is the dependent product of its homogeneous degrees. -/
theorem completion_def (f : X ⟶ Y) :
    Completion δ f = (∀ p : ℕ, Degree δ f p) := rfl

namespace Completion

/-- Completed rational bivariant classes agree if their components agree. -/
@[ext]
theorem ext {f : X ⟶ Y} {a b : Completion δ f}
    (h : ∀ p, a p = b p) : a = b := funext h

end Completion

end AlgebraicGeometry.BivariantClass.Nonnegative.Rational
