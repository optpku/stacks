/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure.Finiteness
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Union
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PointClosure

variable {U X : Scheme.{u}}

/-- The canonical comparison between the two ways of pushing the structure sheaf of a
reduced point closure to the target of a scheme morphism. -/
noncomputable def pushforwardStructureSheafIso (f : U ⟶ X) (x : U) :
    (Scheme.Modules.pushforward f).obj
        (closedSubschemeStructureSheafOn (reducedStructure x).ideal) ≅
      (Scheme.Modules.pushforward (ι (f x))).obj
        ((Scheme.Modules.pushforward (map f x)).obj
          (SheafOfModules.unit (scheme x).ringCatSheaf)) :=
  (Scheme.Modules.pushforwardComp (ι x) f).app
      (SheafOfModules.unit (scheme x).ringCatSheaf) ≪≫
    (Scheme.Modules.pushforwardCongr (map_ι f x).symm).app
      (SheafOfModules.unit (scheme x).ringCatSheaf) ≪≫
    (Scheme.Modules.pushforwardComp (map f x) (ι (f x))).symm.app
      (SheafOfModules.unit (scheme x).ringCatSheaf)

/-- The forward map of `pushforwardStructureSheafIso` is the composite of the two
pushforward-composition comparisons and transport along `map_ι`. -/
theorem pushforwardStructureSheafIso_hom (f : U ⟶ X) (x : U) :
    (pushforwardStructureSheafIso f x).hom =
      (Scheme.Modules.pushforwardComp (ι x) f).hom.app
          (SheafOfModules.unit (scheme x).ringCatSheaf) ≫
        (Scheme.Modules.pushforwardCongr (map_ι f x).symm).hom.app
          (SheafOfModules.unit (scheme x).ringCatSheaf) ≫
        (Scheme.Modules.pushforwardComp (map f x) (ι (f x))).inv.app
          (SheafOfModules.unit (scheme x).ringCatSheaf) := sorry

section

variable [IsLocallyNoetherian U] [IsLocallyNoetherian X]
variable (j : U ⟶ X) [IsOpenImmersion j] (x : U)

/-- For an open immersion of locally Noetherian schemes, the composite pushforward of the
structure sheaf of a reduced point closure is coherent exactly when its pushforward along the
induced map between reduced point closures is coherent. -/
theorem pushforwardStructureSheaf_isCoherent_iff :
    ((Scheme.Modules.pushforward j).obj
        (closedSubschemeStructureSheafOn (reducedStructure x).ideal)).IsCoherent ↔
      ((Scheme.Modules.pushforward (map j x)).obj
        (SheafOfModules.unit (scheme x).ringCatSheaf)).IsCoherent := sorry

end

end AlgebraicGeometry.Scheme.PointClosure
