/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.InverseImage.SquareKan
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.InverseImage.TypeComparison

/-! # Geometric inverse image on the original Type u site

Data are restriction to specified atlas charts, the explicit square-colimit
inverse image, and small-index Ran back to the original site. The owner
comparison evaluates old sections on the actual square maps; it is never
chosen from an existence assertion about arbitrary functors.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PullbackFactory.Geometric

open Squares

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- The actual inverse image in the original universe and on the original site. -/
def inverse : Sheaf (smallEtaleTopology Y) (Type u) ⥤
    Sheaf (smallEtaleTopology X) (Type u) :=
  (TypeComparison.comparison Y).functor ⋙ SquareKan.inverse f ⋙
    (TypeComparison.comparison X).inverse

/-- Compatible-section direct image transported by the same specified sites. -/
def direct : Sheaf (smallEtaleTopology X) (Type u) ⥤
    Sheaf (smallEtaleTopology Y) (Type u) :=
  (TypeComparison.comparison X).functor ⋙ SquareKan.direct f ⋙
    (TypeComparison.comparison Y).inverse

/-- Composition of explicit adjunctions; no admitted adjoint-existence field. -/
def adjunction : inverse f ⊣ direct f :=
  ((TypeComparison.comparison Y).toAdjunction.comp
    (SquareKan.adjunction f)).comp
      (TypeComparison.comparison X).symm.toAdjunction

end AlgebraicGeometry.AlgebraicSpace.PullbackFactory.Geometric
