/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Derived
public import stacks_project.Chap66.Lemma_66_18_3
public import stacks_project.Chap66.Lemma_66_19_9_Exact
public import stacks_project.Chap73.Lemma_73_4_7_Relocalization
public import stacks_project.Chap73.Lemma_73_7_8_Topology
public import stacks_project.Chap84.Lemma_84_5_5_SmallToBig
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FppfEtale.InverseImage

/-! # Fppf/étale inverse images of algebraic spaces -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open AlgebraicGeometry.AlgebraicSpace.FppfEtale
open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology

universe u

/- Lemma 84.6.6: inverse image from the small étale site to the big fppf slice. -/
#check (AlgebraicGeometry.AlgebraicSpace.FppfEtale.aInverseAb :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf ((fppfTopology S).over X) AddCommGrpCat.{u + 1})

#check (AlgebraicGeometry.AlgebraicSpace.FppfEtale.aInverseAbPlus :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf ((fppfTopology S).over X) AddCommGrpCat.{u + 1}))

#check (AlgebraicGeometry.AlgebraicSpace.FppfEtale.sheafPushforwardAdjunction :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    sheafInverseImage AddCommGrpCat.{u + 1} f ⊣ sheafPushforward AddCommGrpCat.{u + 1} f)

end
