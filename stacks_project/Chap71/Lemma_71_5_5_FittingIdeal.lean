module

public import stacks_project.Chap71.Lemma_71_5_1_FittingIdeal

/-!
# Predecessor Fitting ideal sheaves on algebraic spaces

The predecessor of the zeroth Fitting ideal sheaf is the zero ideal sheaf, matching
the scheme-level convention that the Fitting ideal of index `-1` is zero.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The Fitting ideal sheaf one step below the indicated rank, with the predecessor of the
zeroth Fitting ideal sheaf defined to be the zero ideal sheaf. -/
abbrev precedingFittingIdealSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (r : ℕ) : IdealSubobject X :=
  match r with
  | 0 => ⊥
  | r + 1 => fittingIdealSheaf F r

/-- The predecessor of the zeroth Fitting ideal sheaf is the zero ideal sheaf. -/
@[simp]
theorem precedingFittingIdealSheaf_zero {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) : precedingFittingIdealSheaf F 0 = ⊥ :=
  rfl

/-- The predecessor of the `(r + 1)`st Fitting ideal sheaf is the `r`th Fitting ideal sheaf. -/
@[simp]
theorem precedingFittingIdealSheaf_succ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (r : ℕ) :
    precedingFittingIdealSheaf F (r + 1) = fittingIdealSheaf F r :=
  rfl

end AlgebraicGeometry.AlgebraicSpace

