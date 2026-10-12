/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.StrictTransform
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.AffineBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.SectionsWithSupport.Pushforward

/-!
# Pushforward of strict transforms

This file records compatibility between strict transforms and pushforward along affine morphisms.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The morphism between strict-transform ambient schemes induced by base change of a morphism
over the same scheme. -/
abbrev strictTransformBaseChangeMap
    {S S' X Y : Scheme.{u}} (b : S' ⟶ S) (g : X ⟶ Y) (y : Y ⟶ S) :
    strictTransformAmbient b (g ≫ y) ⟶ strictTransformAmbient b y :=
  ((Over.pullback b).map
    (Over.homMk g : Over.mk (g ≫ y) ⟶ Over.mk y)).left

namespace Scheme.Modules

/-- For a blowup, pushforward along the base change of an affine morphism carries the strict
transform of a quasicoherent module to an object isomorphic to the strict transform of its
pushforward. -/
theorem pushforward_strictTransformModule_isomorphic_of_isAffineHom
    {S S' X Y : Scheme.{u}} (I : S.IdealSheafData) (b : S' ⟶ S) [IsBlowup b I]
    (g : X ⟶ Y) (y : Y ⟶ S) [IsAffineHom g]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsIsomorphic
      (((Scheme.Modules.pushforward (strictTransformBaseChangeMap b g y)).obj
        (strictTransformModule b (I.comap b) (g ≫ y) ℱ) :
          (strictTransformAmbient b y).Modules))
      (strictTransformModule b (I.comap b) y ((Scheme.Modules.pushforward g).obj ℱ)) := sorry

end Scheme.Modules

end AlgebraicGeometry
