/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.Complement

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty TopologicalSpace TypeCat
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.openComplementAlong

/-- If `T ≤ T'`, the open complement of `T'` includes into the open complement of
`T`. -/
def mapOfLe {S : Scheme.{u}} {X : AlgebraicSpace S} {T T' : Closeds (Points X)}
    (h : T ≤ T') :
    openComplementAlong X T' ⟶ openComplementAlong X T where
  app U := ofHom fun x ↦ ⟨x.1, sorry⟩
  naturality := sorry

/-- Postcomposing `mapOfLe h` with the open-complement inclusion of `T` recovers
the open-complement inclusion of `T'`. -/
theorem mapOfLe_comp_ι {S : Scheme.{u}} {X : AlgebraicSpace S}
    {T T' : Closeds (Points X)} (h : T ≤ T') :
    mapOfLe h ≫ AlgebraicSpace.openComplementι X T =
      AlgebraicSpace.openComplementι X T' :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.openComplementAlong

