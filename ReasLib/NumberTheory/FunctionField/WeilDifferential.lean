module

public import ReasLib.NumberTheory.FunctionField.Adeles

@[expose] public section

open scoped RatFunc

noncomputable section

universe u

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
variable [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

namespace FunctionField

/-- A Weil differential is a covector vanishing on the diagonal image of `K`. -/
def IsWeilDifferential (μ : AdeleRing k K →ₗ[k] k) : Prop :=
  IsCovector k K μ ∧ ∀ x : K, μ (algebraMap K (AdeleRing k K) x) = 0

/-- The zero linear map is a Weil differential. -/
theorem isWeilDifferential_zero :
    IsWeilDifferential k K (0 : AdeleRing k K →ₗ[k] k) :=
  ⟨⟨0, fun _ _ ↦ rfl⟩, fun _ ↦ rfl⟩

/-- A Weil differential is exactly a covector vanishing on the diagonal image. -/
theorem isWeilDifferential_iff (μ : AdeleRing k K →ₗ[k] k) :
    IsWeilDifferential k K μ ↔
      IsCovector k K μ ∧ ∀ x : K, μ (algebraMap K (AdeleRing k K) x) = 0 :=
  Iff.rfl

end FunctionField
