/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Category.TopCat.DiagramOpens.Constant

@[expose] public section

open CategoryTheory CategoryTheory.Functor Opposite TopologicalSpace TopCat
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialObject

/-- Degree inclusion of a constant simplicial space is continuous. -/
theorem constSpace_fiber_isContinuous (X : TopCat.{u}) (c : SimplexCategoryᵒᵖ) :
    (DiagramOpens.fiber (constSpace X) c).IsContinuous
      (Opens.grothendieckTopology X) (zariskiTopology (constSpace X)) :=
  fiber_isContinuous (constSpace X) c

/-- Degree inclusion of a constant simplicial space is cocontinuous. -/
theorem constSpace_fiber_isCocontinuous (X : TopCat.{u}) (c : SimplexCategoryᵒᵖ) :
    (DiagramOpens.fiber (constSpace X) c).IsCocontinuous
      (Opens.grothendieckTopology X) (zariskiTopology (constSpace X)) :=
  fiber_isCocontinuous (constSpace X) c

variable (X : TopCat.{u})

#check (CategoryTheory.SimplicialObject.constProjection X :
  zariskiSite (constSpace X) ⥤ Opens X)
#check (CategoryTheory.SimplicialObject.toCosimplicial X (Type u) :
  Sheaf (zariskiTopology (constSpace X)) (Type u) ⥤
    CosimplicialObject (Sheaf (Opens.grothendieckTopology X) (Type u)))

end CategoryTheory.SimplicialObject
