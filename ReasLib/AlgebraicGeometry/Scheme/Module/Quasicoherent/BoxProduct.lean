/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

/-- The external product `A ⊠ B` of quasicoherent modules on a fibre product. -/
noncomputable def boxProduct {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (A : Scheme.QCoh X) (B : Scheme.QCoh Y) :
    Scheme.QCoh (Limits.pullback f g) :=
  (tensorRight ((pullback (Limits.pullback.snd f g)).obj B)).obj
    ((pullback (Limits.pullback.fst f g)).obj A)

/-- The underlying module of `boxProduct f g A B` is
`pr₁^* A ⊗ pr₂^* B` on `Limits.pullback f g`. -/
theorem boxProduct_obj {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (A : Scheme.QCoh X) (B : Scheme.QCoh Y) :
    (boxProduct f g A B).obj =
      ((pullback (Limits.pullback.fst f g)).obj A).obj ⊗
        ((pullback (Limits.pullback.snd f g)).obj B).obj := sorry

end AlgebraicGeometry.Scheme.QCoh
