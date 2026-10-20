module

public import ReasLib.AlgebraicGeometry.Polarized.Over
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Base
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

/-!
# Algebraicity of stacks of polarized proper schemes

The stack of polarized proper schemes is algebraic, as is the stack of
polarized families with a base map to any algebraic space over `Spec ℤ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- The category of polarized proper schemes is an algebraic stack over `Spec ℤ`. -/
@[stacks 0D4X]
instance instAlgebraicStack : AlgebraicStack toGroupoidsOverSpecZ :=
  sorry

namespace polarizedOver

/-- For every algebraic space `B` over `Spec ℤ`, polarized families with a base
map to `B` form an algebraic stack over `Spec ℤ`. -/
@[stacks 0D4X]
instance instAlgebraicStack (B : AlgebraicSpace specZ) :
    AlgebraicStack (toGroupoids B) :=
  sorry

end polarizedOver

/-- The structure morphism from the stack of polarized proper schemes to
`Spec ℤ` is quasi-separated. -/
@[stacks 0DPU]
instance instQuasiSeparated_baseProjection :
    AlgebraicStack.QuasiSeparated
      (baseProjection.{u + 1, u, u + 1} toGroupoidsOverSpecZ) :=
  sorry

/-- The structure morphism from the stack of polarized proper schemes to
`Spec ℤ` is locally of finite presentation. -/
@[stacks 0DPU]
instance instLocallyOfFinitePresentation_baseProjection :
    AlgebraicStack.LocallyOfFinitePresentation
      (baseProjection.{u + 1, u, u + 1} toGroupoidsOverSpecZ) :=
  sorry

end AlgebraicGeometry.Polarized
