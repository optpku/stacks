/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.Pointed

/-!
# Right adjoint of pointed compact-support direct image

An explicit adjoint-existence certificate determines the pointed upper shriek and its adjunction.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}}

/-- The pointed upper shriek selected from an explicit adjoint-existence certificate. -/
def pointedUpperShriek (f : X ⟶ Y) [LocallyQuasiFinite f]
    [HasSheafify Y.smallEtaleTopology Pointed.{u}]
    (h : (pointedLowerShriek f).IsLeftAdjoint) :
    Sheaf Y.smallEtaleTopology Pointed.{u} ⥤ Sheaf X.smallEtaleTopology Pointed.{u} :=
  @Functor.rightAdjoint _ _ _ _ (pointedLowerShriek f) h

/-- The adjunction determined by the supplied certificate for pointed lower shriek. -/
def pointedLowerShriekAdjunction (f : X ⟶ Y) [LocallyQuasiFinite f]
    [HasSheafify Y.smallEtaleTopology Pointed.{u}]
    (h : (pointedLowerShriek f).IsLeftAdjoint) :
    pointedLowerShriek f ⊣ pointedUpperShriek f h :=
  @Adjunction.ofIsLeftAdjoint _ _ _ _ (pointedLowerShriek f) h

/-- The hom-equivalence of the pointed compact-support adjunction. -/
def pointedLowerShriekAdjunction_homEquiv (f : X ⟶ Y) [LocallyQuasiFinite f]
    [HasSheafify Y.smallEtaleTopology Pointed.{u}]
    (h : (pointedLowerShriek f).IsLeftAdjoint)
    (G : Sheaf X.smallEtaleTopology Pointed.{u})
    (H : Sheaf Y.smallEtaleTopology Pointed.{u}) :
    ((pointedLowerShriek f).obj G ⟶ H) ≃
      (G ⟶ (pointedUpperShriek f h).obj H) :=
  (pointedLowerShriekAdjunction f h).homEquiv G H

/-- The upper shriek of a pointed skyscraper is a fibrewise product of skyscrapers. -/
theorem pointedUpperShriekSkyscraperIso_nonempty (f : X ⟶ Y)
    [LocallyQuasiFinite f] [HasSheafify Y.smallEtaleTopology Pointed.{u}]
    (h : (pointedLowerShriek f).IsLeftAdjoint) (ybar : GeometricPoint Y) :
    Nonempty ((GeometricPoint.toSmallEtalePoint ybar).skyscraperSheafFunctor ⋙
        pointedUpperShriek f h ≅ pointedSkyscraperProduct f ybar) := sorry

end AlgebraicGeometry.Scheme.Etale

end
