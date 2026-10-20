/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace

/-! # Transport of open subspaces along isomorphisms -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Postcomposing an open-subspace inclusion with an ambient isomorphism is an open immersion. -/
theorem OpenSubspace.mapIso_isOpenImmersion {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (e : X ≅ Y) (U : OpenSubspace X) : IsOpenImmersion (U.ι ≫ e.hom) :=
  sorry

/-- Transport an open subspace along an isomorphism of ambient algebraic spaces,
keeping the same underlying space and postcomposing the inclusion. -/
def OpenSubspace.mapIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} (e : X ≅ Y)
    (U : OpenSubspace X) : OpenSubspace Y where
  X := U.X
  ι := U.ι ≫ e.hom
  isOpenImmersion := OpenSubspace.mapIso_isOpenImmersion e U

/-- The inclusion of `OpenSubspace.mapIso e U` is `U.ι ≫ e.hom`. -/
theorem OpenSubspace.mapIso_ι {S : Scheme.{u}} {X Y : AlgebraicSpace S} (e : X ≅ Y)
    (U : OpenSubspace X) : (OpenSubspace.mapIso e U).ι = U.ι ≫ e.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
