/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.DirectImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Coreflector.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.CupProduct

/-! # Tensor comparison for quasi-coherent direct image -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

namespace LQCohFbc

/-- Degree-0 naive relative cup product in `LQCoh^{fbc}(𝒪_Y)`:
`c : f_* F ⊗ f_* G ⟶ f_*(F ⊗ G)`, with source and target in `LQCoh^{fbc}`. -/
def naiveRelativeCupProduct {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f]
    (F G : QCoh X) :
    tensor
        ((directImage f).obj ((QCoh.toLQCohFbc X).obj F))
        ((directImage f).obj ((QCoh.toLQCohFbc X).obj G)) ⟶
      (directImage f).obj ((QCoh.toLQCohFbc X).obj (QCoh.Fppf.tensor F G)) :=
  ObjectProperty.homMk
    (RingedSite.ToposHom.ModulePushforward.naiveCupProduct (etaleRingedToposHom f)
        ((inclusion X).obj ((QCoh.toLQCohFbc X).obj F))
        ((inclusion X).obj ((QCoh.toLQCohFbc X).obj G)) ≫
      (etaleModuleDirectImage f).map (QCoh.toLQCohFbc_tensorator_hom F G))

/-- The underlying étale morphism of `naiveRelativeCupProduct` is the étale
cup product followed by direct image of the inclusion tensorator. -/
theorem naiveRelativeCupProduct_hom {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f]
    (F G : QCoh X) :
    (naiveRelativeCupProduct f F G).hom =
      RingedSite.ToposHom.ModulePushforward.naiveCupProduct (etaleRingedToposHom f)
          ((inclusion X).obj ((QCoh.toLQCohFbc X).obj F))
          ((inclusion X).obj ((QCoh.toLQCohFbc X).obj G)) ≫
        (etaleModuleDirectImage f).map (QCoh.toLQCohFbc_tensorator_hom F G) :=
  rfl

/-- The tensor of the two adjunction counits from quasi-coherent direct images to
étale direct images. -/
def directImageTensorCounit {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f]
    (adj : QCoh.toLQCohFbc Y ⊣ toQCoh Y) (F G : QCoh X) :
    tensor
        ((QCoh.toLQCohFbc Y).obj ((QCoh.directImage f).obj F))
        ((QCoh.toLQCohFbc Y).obj ((QCoh.directImage f).obj G)) ⟶
      tensor
        ((directImage f).obj ((QCoh.toLQCohFbc X).obj F))
        ((directImage f).obj ((QCoh.toLQCohFbc X).obj G)) :=
  tensorCounit adj
    ((directImage f).obj ((QCoh.toLQCohFbc X).obj F))
    ((directImage f).obj ((QCoh.toLQCohFbc X).obj G))

/-- `directImageTensorCounit` is the tensor of the two counit components. -/
theorem directImageTensorCounit_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f]
    (adj : QCoh.toLQCohFbc Y ⊣ toQCoh Y) (F G : QCoh X) :
    directImageTensorCounit f adj F G =
      tensorHom
        (adj.counit.app ((directImage f).obj ((QCoh.toLQCohFbc X).obj F)))
        (adj.counit.app ((directImage f).obj ((QCoh.toLQCohFbc X).obj G))) :=
  rfl

/-- Naturality of the `LQCoh^{fbc}` naive cup product in both quasi-coherent
arguments. -/
theorem naiveRelativeCupProduct_natural {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f]
    {F F' G G' : QCoh X} (α : F ⟶ F') (β : G ⟶ G') :
    tensorHom
        ((directImage f).map ((QCoh.toLQCohFbc X).map α))
        ((directImage f).map ((QCoh.toLQCohFbc X).map β)) ≫
      naiveRelativeCupProduct f F' G' =
    naiveRelativeCupProduct f F G ≫
      (directImage f).map ((QCoh.toLQCohFbc X).map (CategoryTheory.MonoidalCategory.tensorHom α β)) :=
  sorry

end LQCohFbc

namespace QCoh

/-- The quasi-coherent tensor comparison is the coreflector tensorator followed by
coreflection of the relative cup product. -/
def directImage_tensorComparison {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f]
    (adj : toLQCohFbc Y ⊣ LQCohFbc.toQCoh Y) (F G : QCoh X) :
    Fppf.tensor ((directImage f).obj F) ((directImage f).obj G) ⟶
      (directImage f).obj (Fppf.tensor F G) :=
  LQCohFbc.toQCoh_μ adj
      ((LQCohFbc.directImage f).obj ((toLQCohFbc X).obj F))
      ((LQCohFbc.directImage f).obj ((toLQCohFbc X).obj G)) ≫
    (LQCohFbc.toQCoh Y).map (LQCohFbc.naiveRelativeCupProduct f F G)

/-- `directImage_tensorComparison` is `μ` followed by `Q(c)`. -/
theorem directImage_tensorComparison_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f]
    (adj : toLQCohFbc Y ⊣ LQCohFbc.toQCoh Y) (F G : QCoh X) :
    directImage_tensorComparison f adj F G =
      LQCohFbc.toQCoh_μ adj
          ((LQCohFbc.directImage f).obj ((toLQCohFbc X).obj F))
          ((LQCohFbc.directImage f).obj ((toLQCohFbc X).obj G)) ≫
        (LQCohFbc.toQCoh Y).map (LQCohFbc.naiveRelativeCupProduct f F G) :=
  rfl

/-- The quasi-coherent direct-image tensor comparison included into the category of
locally quasi-coherent modules with flat base change. -/
def directImage_tensorComparison_included {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f]
    (adj : toLQCohFbc Y ⊣ LQCohFbc.toQCoh Y) (F G : QCoh X) :
    LQCohFbc.tensor
        ((toLQCohFbc Y).obj ((directImage f).obj F))
        ((toLQCohFbc Y).obj ((directImage f).obj G)) ⟶
      (toLQCohFbc Y).obj ((directImage f).obj (Fppf.tensor F G)) :=
  toLQCohFbc_tensorator ((directImage f).obj F) ((directImage f).obj G) ≫
    (toLQCohFbc Y).map (directImage_tensorComparison f adj F G)

/-- `directImage_tensorComparison_included` is the inclusion tensorator
followed by `i(Q(c))`. -/
theorem directImage_tensorComparison_included_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f]
    (adj : toLQCohFbc Y ⊣ LQCohFbc.toQCoh Y) (F G : QCoh X) :
    directImage_tensorComparison_included f adj F G =
      toLQCohFbc_tensorator ((directImage f).obj F) ((directImage f).obj G) ≫
        (toLQCohFbc Y).map (directImage_tensorComparison f adj F G) :=
  rfl

end QCoh

namespace QCoh

/-- For a quasi-compact quasi-separated morphism of algebraic stacks, the relative cup
product and its quasi-coherent coreflection form a commutative square with the counits. -/
@[stacks 0GQR]
theorem directImage_tensor_commSq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f]
    (F G : QCoh X) :
    CommSq
      (LQCohFbc.directImageTensorCounit f (toLQCohFbcAdjunction Y) F G)
      (directImage_tensorComparison_included f (toLQCohFbcAdjunction Y) F G)
      (LQCohFbc.naiveRelativeCupProduct f F G)
      ((toLQCohFbcAdjunction Y).counit.app
        ((LQCohFbc.directImage f).obj ((toLQCohFbc X).obj (Fppf.tensor F G)))) :=
  sorry

/-- The canonical tensor comparison on quasi-coherent direct images is natural
simultaneously in both quasi-coherent arguments. -/
@[stacks 0GQR]
theorem directImage_tensor_natural {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f]
    {F F' G G' : QCoh X} (α : F ⟶ F') (β : G ⟶ G') :
    tensorHom ((directImage f).map α) ((directImage f).map β) ≫
      directImage_tensorComparison f (toLQCohFbcAdjunction Y) F' G' =
    directImage_tensorComparison f (toLQCohFbcAdjunction Y) F G ≫
      (directImage f).map (tensorHom α β) :=
  sorry

end QCoh

end AlgebraicGeometry.GroupoidsOver
