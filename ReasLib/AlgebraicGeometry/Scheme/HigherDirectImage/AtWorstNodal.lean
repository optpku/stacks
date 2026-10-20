/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AtWorstNodal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.StructureSheaf

/-! # Higher direct images in proper connected nodal families -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AtWorstNodal

/-- The canonical degree-one base-change map for the structure module, obtained
from the generic comparison and the structure-module pullback isomorphism. -/
def higherDirectImageOneBaseChangeMap
    {X S : Scheme.{u}} (f : X ⟶ S) {S' : Scheme.{u}} (g : S' ⟶ S) :
    (Scheme.Modules.pullback g).obj
        (RingedSpace.Hom.higherDirectImageModule f.toShHom
          (SheafOfModules.unit X.ringCatSheaf) 1) ⟶
      RingedSpace.Hom.higherDirectImageModule (pullback.snd f g).toShHom
        (SheafOfModules.unit (pullback f g).ringCatSheaf) 1 :=
  RingedSpace.Hom.higherDirectImageModuleBaseChangeMap
      ((CategoryTheory.IsPullback.of_hasPullback f g).toCommSq.map
        (Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToSheafedSpace))
      (SheafOfModules.unit X.ringCatSheaf) 1 ≫
    RingedSpace.Hom.higherDirectImageModuleMap (pullback.snd f g).toShHom
      (Scheme.Modules.pullbackStructureSheafIso (pullback.fst f g)).hom 1

/-- For a proper at-worst-nodal morphism with geometrically connected fibres,
the canonical map `𝒪_S ⟶ f_*𝒪_X` is an isomorphism. -/
@[instance]
theorem structureSheafMap_isIso
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [AtWorstNodal f] [GeometricallyConnected f] :
    IsIso (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom) :=
  Scheme.Hom.StructureSheaf.isIso_of_geometricallyReduced_geometricallyConnected f

/-- The canonical structure-sheaf pushforward map remains invertible after
every base change of a proper connected nodal family. -/
theorem baseChange_structureSheafMap_isIso
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [AtWorstNodal f] [GeometricallyConnected f]
    {S' : Scheme.{u}} (g : S' ⟶ S) :
    IsIso (RingedSpace.Hom.commRingSheafPushforwardMap (pullback.snd f g).toShHom) :=
  Scheme.Hom.StructureSheaf.baseChange_isIso_of_geometricallyReduced_geometricallyConnected f g

/-- The first structure-sheaf higher direct image of a proper connected nodal
family is finite locally free on the entire base. -/
@[instance]
theorem higherDirectImageOne_isFiniteLocallyFree
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [AtWorstNodal f] [GeometricallyConnected f] :
    SheafOfModules.IsFiniteLocallyFree
      (RingedSpace.Hom.higherDirectImageModule f.toShHom
        (SheafOfModules.unit X.ringCatSheaf) 1) := sorry

/-- Formation of the first structure-sheaf higher direct image commutes with
arbitrary base change through the specified canonical comparison. -/
theorem higherDirectImageOne_commutesWithBaseChange
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [AtWorstNodal f] [GeometricallyConnected f]
    {S' : Scheme.{u}} (g : S' ⟶ S) :
    IsIso (higherDirectImageOneBaseChangeMap f g) := sorry

/-- All structure-sheaf higher direct images in degrees at least two vanish
for a proper connected nodal family. -/
theorem higherDirectImage_isZero_of_two_le
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [AtWorstNodal f] [GeometricallyConnected f]
    (q : ℕ) (hq : 2 ≤ q) :
    IsZero (RingedSpace.Hom.higherDirectImageModule f.toShHom
      (SheafOfModules.unit X.ringCatSheaf) q) := sorry

end AlgebraicGeometry.AtWorstNodal
