/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.DirectImage.Tensor
import StacksCheckRecall

/-! # Tensor comparison for quasi-coherent direct image -/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

/- Remark 103.11.3: the canonical tensor comparison square. -/
@[stacks 0GQR] #check (AlgebraicGeometry.GroupoidsOver.QCoh.directImage_tensor_commSq :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f]
    (F G : QCoh X),
    CommSq
      (LQCohFbc.directImageTensorCounit f (toLQCohFbcAdjunction Y) F G)
      (directImage_tensorComparison_included f (toLQCohFbcAdjunction Y) F G)
      (LQCohFbc.naiveRelativeCupProduct f F G)
      ((toLQCohFbcAdjunction Y).counit.app
        ((LQCohFbc.directImage f).obj ((toLQCohFbc X).obj (Fppf.tensor F G)))))

#check (AlgebraicGeometry.GroupoidsOver.QCoh.directImage_tensor_natural :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f]
    {F F' G G' : QCoh X} (α : F ⟶ F') (β : G ⟶ G'),
    tensorHom ((directImage f).map α) ((directImage f).map β) ≫
      directImage_tensorComparison f (toLQCohFbcAdjunction Y) F' G' =
    directImage_tensorComparison f (toLQCohFbcAdjunction Y) F G ≫
      (directImage f).map (tensorHom α β))

end AlgebraicGeometry.GroupoidsOver.QCoh
