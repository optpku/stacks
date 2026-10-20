module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme.TensorSplitting
public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.LineBundle

/-!
# Geometry of the first projection of a tensor-section splitting

The first factor zero scheme in a tensor-section splitting is a line bundle
over the original zero scheme. This file records the geometric properties of
its projection.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.TensorSectionSplitting

variable {Y : Scheme.{u}} {L₁ L₂ : Y.Modules}
variable [Modules.Invertible L₁] [Modules.Invertible L₂]
variable {s : (L₁ ⊗ L₂).sections}

/-- The first projection in a tensor-section splitting is of finite type. -/
theorem p₁_finiteType (C : TensorSectionSplitting L₁ L₂ s) :
    Hom.FiniteType C.p₁ := sorry

/-- The first projection in a tensor-section splitting is flat. -/
theorem p₁_flat (C : TensorSectionSplitting L₁ L₂ s) : Flat C.p₁ := sorry

/-- The first projection in a tensor-section splitting has relative dimension one. -/
theorem p₁_relativeDimension (C : TensorSectionSplitting L₁ L₂ s) :
    Hom.RelativeDimension C.p₁ 1 := sorry

end AlgebraicGeometry.Scheme.TensorSectionSplitting
