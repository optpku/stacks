/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Topology
public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Projection

/-!
# Structure sheaf of a category fibred in groupoids

A category fibred in groupoids over `(Sch/S)_fppf` inherits the big fppf
structure sheaf by precomposition with its projection.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The structure sheaf of a category fibred in groupoids over `(Sch/S)_fppf`
is the inverse image of the big fppf structure sheaf along its projection. -/
def structureSheaf (X : GroupoidsOver S) :
    Sheaf (fppfTopology X) RingCat.{u} :=
  (X.p.sheafPushforwardContinuous RingCat.{u}
      (fppfTopology X) (Scheme.fppfTopology.over S)).obj
    (StandardTopology.Big.structureSheaf .fppf S)

/-- The structure sheaf is obtained by continuous precomposition of the big
fppf structure sheaf with the projection. -/
theorem structureSheaf_def (X : GroupoidsOver S) :
    structureSheaf X =
      (X.p.sheafPushforwardContinuous RingCat.{u}
          (fppfTopology X) (Scheme.fppfTopology.over S)).obj
        (StandardTopology.Big.structureSheaf .fppf S) :=
  sorry

/-- Sections of the structure sheaf at an object agree with sections of the
big fppf structure sheaf at its image under the projection. -/
theorem structureSheaf_obj_eq_big {X : GroupoidsOver S} (x : X.total) :
    (structureSheaf X).obj.obj (op x) =
      (StandardTopology.Big.structureSheaf .fppf S).obj.obj (op (X.p.obj x)) :=
  sorry

/-- The value of the structure sheaf at an object lying over a scheme is the
global-sections ring of that scheme. -/
theorem structureSheaf_obj {X : GroupoidsOver S} (x : X.total) :
    (structureSheaf X).obj.obj (op x) = RingCat.of Γ((X.p.obj x).left, ⊤) :=
  sorry

/-- The fppf site of a category fibred in groupoids, equipped with its
structure sheaf. -/
abbrev ringedSite (X : GroupoidsOver S) :=
  RingedSite.ofRingSheaf (fppfTopology X) (structureSheaf X)

/-- The structure sheaf of the fppf ringed site is the structure sheaf of the
category fibred in groupoids. -/
theorem ringedSite_structureSheaf (X : GroupoidsOver S) :
    (ringedSite X).structureSheaf = structureSheaf X :=
  sorry

end AlgebraicGeometry.GroupoidsOver

