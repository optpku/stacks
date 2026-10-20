/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.OpenSubspace

/-- The locally closed subspace underlying an open subspace. -/
def toLocallyClosed {S : Scheme.{u}} {F : AlgebraicSpace S} (W : OpenSubspace F) :
    LocallyClosedSubspace F where
  X := W.X
  ι := W.ι
  isImmersion := @IsImmersion.ofIsOpenImmersion S W.X F W.ι W.isOpenImmersion

/-- The inclusion of `toLocallyClosed W` is the open inclusion of `W`. -/
theorem toLocallyClosed_ι {S : Scheme.{u}} {F : AlgebraicSpace S}
    (W : OpenSubspace F) : W.toLocallyClosed.ι = W.ι :=
  rfl

/-- The underlying algebraic space of `toLocallyClosed W` is that of `W`. -/
theorem toLocallyClosed_X {S : Scheme.{u}} {F : AlgebraicSpace S}
    (W : OpenSubspace F) : W.toLocallyClosed.X = W.X :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.OpenSubspace

namespace AlgebraicGeometry.AlgebraicSpace.ClosedSubspace

/-- The locally closed subspace underlying a closed subspace. -/
def toLocallyClosed {S : Scheme.{u}} {F : AlgebraicSpace S} (C : ClosedSubspace F) :
    LocallyClosedSubspace F where
  X := C.X
  ι := C.ι
  isImmersion := @IsImmersion.ofIsClosedImmersion S C.X F C.ι C.isClosedImmersion

/-- The inclusion of `toLocallyClosed C` is the closed inclusion of `C`. -/
theorem toLocallyClosed_ι {S : Scheme.{u}} {F : AlgebraicSpace S}
    (C : ClosedSubspace F) : C.toLocallyClosed.ι = C.ι :=
  rfl

/-- The underlying algebraic space of `toLocallyClosed C` is that of `C`. -/
theorem toLocallyClosed_X {S : Scheme.{u}} {F : AlgebraicSpace S}
    (C : ClosedSubspace F) : C.toLocallyClosed.X = C.X :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.ClosedSubspace

