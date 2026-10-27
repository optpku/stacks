/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Pullback
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.DirectImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Quasicoherent

/-! # Finite presentation under module pullback -/

@[expose] public section

open CategoryTheory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
  [AlgebraicStack X] [AlgebraicStack Y]

/-- Finite presentation is preserved by pullback of fppf modules. -/
instance modulePullback_isFinitePresentation (f : X ⟶ Y) (F : fppfModules Y)
    [F.IsFinitePresentation] :
    ((modulePullback f).obj F).IsFinitePresentation := sorry

/-- Finite presentation is preserved by étale inverse image. -/
instance etaleModuleInverseImage_isFinitePresentation (f : X ⟶ Y)
    (F : etaleModules Y) [F.IsFinitePresentation] :
    ((etaleModuleInverseImage f).obj F).IsFinitePresentation := sorry

end AlgebraicGeometry.GroupoidsOver
