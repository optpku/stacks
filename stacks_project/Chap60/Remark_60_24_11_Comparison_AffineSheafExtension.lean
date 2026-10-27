/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Sheaf.AffineBasis

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace CrystallineAffineSheafExtension
export AlgebraicGeometry.Scheme.AffineSheaf (baseSheafPreadditive affineInclusion affineBasis extend extend_affine hom_ext)
end CrystallineAffineSheafExtension
variable (Y : Scheme.{u})
#check (AlgebraicGeometry.Scheme.AffineSheaf.affineBasis Y :
  TopologicalSpace.Opens.IsBasis (Set.range (fun U : Y.affineOpens ↦ U.1)))
