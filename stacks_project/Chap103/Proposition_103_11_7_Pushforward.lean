/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Abelian
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.HigherDirectImage

/-! # Quasi-coherent higher-direct-image compatibility checks -/

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open scoped Bicategory

universe u

variable {S : Scheme.{u}}

#check ((fun {_ _} _ _ f _ _ i F =>
  AlgebraicGeometry.GroupoidsOver.qCohHigherDirectImage_mem_lqcohFbc f i F) :
  ∀ {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (i : ℕ) (F : QCoh X),
    lqcohFbc Y
      ((QCoh.inclusion X ⋙
          AlgebraicStack.fppfHigherDirectImageFunctor f i ⋙
          restriction Y).obj F))

#check ((fun {_ _} _ _ f _ _ i =>
  AlgebraicGeometry.GroupoidsOver.qCohHigherDirectImageFunctor f i) :
  ∀ {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ),
    QCoh X ⥤ QCoh Y)

#check ((fun {_ _} _ _ f _ _ i =>
  AlgebraicGeometry.GroupoidsOver.qCohHigherDirectImageFunctor_eq f i) :
  ∀ {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f] (i : ℕ),
    qCohHigherDirectImageFunctor f i =
      (lqcohFbc Y).lift
          (QCoh.inclusion X ⋙
            AlgebraicStack.fppfHigherDirectImageFunctor f i ⋙ restriction Y)
          (qCohHigherDirectImage_mem_lqcohFbc f i) ⋙
        LQCohFbc.toQCoh Y)

#check ((fun {_ _} _ _ f _ _ F i =>
  AlgebraicGeometry.GroupoidsOver.qCohHigherDirectImage f F i) :
  ∀ {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (F : QCoh X) (i : ℕ),
    QCoh Y)

#check ((fun {_ _} _ _ f _ _ F i =>
  AlgebraicGeometry.GroupoidsOver.qCohHigherDirectImage_eq f F i) :
  ∀ {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (F : QCoh X) (i : ℕ),
    qCohHigherDirectImage f F i = (qCohHigherDirectImageFunctor f i).obj F)
