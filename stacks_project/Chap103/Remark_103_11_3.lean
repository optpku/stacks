/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CommSq
public import stacks_project.Chap103.Remark_103_11_3_CupProduct

/-!
# Tensor comparison for quasi-coherent direct image

For a quasi-compact quasi-separated morphism of algebraic stacks, the naive
relative cup product in degree 0 compares the tensor of quasi-coherent
direct images with the tensor of étale direct images.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

namespace QCoh

/-- Remark 103.11.3 (1): let `f : X ⟶ Y` be a quasi-compact and quasi-separated
morphism of algebraic stacks, and let `F`, `G` be in `QCoh(𝒪_X)`. There is a
canonical commutative square in `LQCoh^{fbc}(𝒪_Y)` whose right vertical arrow
`c` is the degree-0 naive relative cup product
`f_* F ⊗ f_* G ⟶ f_*(F ⊗ G)`, whose source and target lie in `LQCoh^{fbc}`,
and whose left vertical arrow is `Q(c)` after the tensorator `μ` of `Q`. -/
@[stacks 0GQR]
theorem directImage_tensor_commSq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (adj : toLQCohFbc Y ⊣ LQCohFbc.toQCoh Y) (F G : QCoh X) :
    CommSq
      (LQCohFbc.directImageTensorCounit f adj F G)
      (directImage_tensorComparison_included f adj F G)
      (LQCohFbc.naiveRelativeCupProduct f F G)
      (adj.counit.app
        ((LQCohFbc.directImage f).obj ((toLQCohFbc X).obj (tensor F G)))) :=
  sorry

/-- Remark 103.11.3 (2): the degree-0 naive relative cup product, and the
induced quasi-coherent comparison obtained by applying `Q`, are functorial in
`F` and `G`. -/
@[stacks 0GQR]
theorem directImage_tensor_natural {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (adj : toLQCohFbc Y ⊣ LQCohFbc.toQCoh Y)
    {F F' G G' : QCoh X} (α : F ⟶ F') (β : G ⟶ G') :
    tensorHom ((directImage f).map α) ((directImage f).map β) ≫
      directImage_tensorComparison f adj F' G' =
    directImage_tensorComparison f adj F G ≫
      (directImage f).map (tensorHom α β) :=
  sorry

end QCoh

end AlgebraicGeometry.GroupoidsOver
