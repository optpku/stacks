/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal

/-!
# Tensor of a module with the pullback of a module on algebraic spaces

The source module `F ⊗_{𝒪_X} f^* G` is the monoidal tensor of `F` with the
module pullback of `G`, obtained by transporting `moduleTensor` along the
commutative presentation of `𝒪_X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The tensor product of an `𝒪_X`-module with the pullback of an `𝒪_Y`-module. -/
noncomputable def tensorPullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y) (G : Y.Modules) : X.Modules :=
  tensorObj F ((pullback f).obj G)

/-- `tensorPullback F f G` is the commutative presentation tensor of `F` with
`f^* G`, transported along `toCommModules` / `ofCommModules`. -/
theorem tensorPullback_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y) (G : Y.Modules) :
    tensorPullback F f G =
      (ofCommModules X).obj
        (tensorObj ((toCommModules X).obj F)
          ((toCommModules X).obj ((pullback f).obj G))) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules
