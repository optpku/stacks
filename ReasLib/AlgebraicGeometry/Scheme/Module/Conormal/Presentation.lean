/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.SquareZeroExtension

/-!
# Presentation maps for conormal sheaves of schemes

A commutative square of scheme morphisms induces an adjoint-side map between the presentation
sheaves of first-order thickenings. This map commutes with the projections to the structure
sheaves.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.Conormal

variable {X X' Y Y' : Scheme.{u}}

/-- A commutative square of scheme morphisms induces a commutative square of the associated
ringed-space morphisms. -/
theorem toShHom_commSq {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y}
    {a' : X' ⟶ Y'} (sq : CommSq a i j a') :
    CommSq a.toShHom i.toShHom j.toShHom a'.toShHom := sorry

/-- The equality of base maps underlying a commutative square of scheme morphisms. -/
theorem toShHom_base_commutes {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y}
    {a' : X' ⟶ Y'} (sq : CommSq a i j a') :
    (a.toShHom ≫ j.toShHom).hom.base =
      (i.toShHom ≫ a'.toShHom).hom.base := sorry

/-- The adjoint-side map between inverse-image presentation sheaves induced by a commutative
square of schemes. -/
noncomputable def presentationMap {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y}
    {a' : X' ⟶ Y'} (sq : CommSq a i j a') :
    IsFirstOrderThickening.presentationSheaf j ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} a.base).obj
        (IsFirstOrderThickening.presentationSheaf i) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} a.base).homEquiv _ _)
    ((RingedSpace.Hom.StructureSheaf.compIso a.toShHom j.toShHom).hom ≫
      (TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
        (toShHom_base_commutes sq)).hom.app Y'.sheaf ≫
      (RingedSpace.Hom.StructureSheaf.compIso i.toShHom a'.toShHom).inv ≫
      (TopCat.Sheaf.pullback CommRingCat.{u} i.base).map
        (RingedSpace.Hom.inverseImageStructureSheafHomComm a'.toShHom))

/-- The presentation map commutes with the projections to the reduced structure sheaves. -/
theorem presentationMap_square {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y}
    {a' : X' ⟶ Y'} (sq : CommSq a i j a') :
    CommSq (presentationMap sq) (IsFirstOrderThickening.presentationProjection j)
      ((TopCat.Sheaf.pushforward CommRingCat.{u} a.base).map
        (IsFirstOrderThickening.presentationProjection i))
      (RingedSpace.Hom.commRingSheafPushforwardMap a.toShHom) := sorry

end AlgebraicGeometry.Scheme.Hom.Conormal
