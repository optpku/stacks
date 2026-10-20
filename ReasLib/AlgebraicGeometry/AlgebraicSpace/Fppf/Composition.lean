/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.Big

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Fppf.Big

/-- The inverse image of the composite of big fppf morphisms of topoi is
canonically isomorphic to the inverse image induced by the composite morphism
of algebraic spaces. -/
noncomputable def morphismOfTopoi_comp_inverseImageIso
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (MorphismOfTopoiIn.comp
      (CategoryTheory.Over.Site.morphismOfTopoi.{u + 1, u + 1, u + 1} (fppfTopology S) g)
      (CategoryTheory.Over.Site.morphismOfTopoi.{u + 1, u + 1, u + 1} (fppfTopology S) f)).inverseImage ≅
        (CategoryTheory.Over.Site.morphismOfTopoi.{u + 1, u + 1, u + 1}
          (fppfTopology S) (f ≫ g)).inverseImage :=
  (fppfTopology S).overMapPullbackComp (Type (u + 1)) f g

end AlgebraicGeometry.AlgebraicSpace.Fppf.Big
