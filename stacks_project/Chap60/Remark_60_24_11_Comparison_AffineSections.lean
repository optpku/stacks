/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.AffineSections

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace CrystallineAffineSections
export AlgebraicGeometry.Scheme.Modules.Affine (chart_image_top pullbackSectionsIso)
end CrystallineAffineSections
variable {Y : Scheme.{u}} (U : Y.affineOpens) (M : Y.Modules)
#check (AlgebraicGeometry.Scheme.Modules.Affine.pullbackSectionsIso U M :
  M.presheaf.obj (op U.1) ≅
    ((Scheme.Modules.pullback U.property.fromSpec).obj M).presheaf.obj (op ⊤))
