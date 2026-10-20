/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.Big

/-!
# Lemma 73.7.8

A morphism of algebraic spaces over a scheme induces a morphism of big fppf
topoi.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Fppf.Big
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)

/- Lemma 73.7.8 -/
@[stacks 0DFD] #check
  (CategoryTheory.Over.Site.morphismOfTopoi (fppfTopology S) f :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, u + 1}
      ((fppfTopology S).over X) ((fppfTopology S).over Y))

/- Postcomposition and pullback are the functors between the big fppf slices. -/
#check (Over.map f : Over Y ⥤ Over X)

#check (Over.pullback f : Over X ⥤ Over Y)

/- Postcomposition is cocontinuous and continuous, pullback is continuous, and
the two functors form the canonical adjunction. -/
#check
  (inferInstance :
    Functor.IsCocontinuous (Over.map f)
      ((fppfTopology S).over Y) ((fppfTopology S).over X))

#check
  (inferInstance :
    Functor.IsContinuous (Over.map f)
      ((fppfTopology S).over Y) ((fppfTopology S).over X))

#check
  (inferInstance :
    Functor.IsContinuous (Over.pullback f)
      ((fppfTopology S).over X) ((fppfTopology S).over Y))

#check
  (Over.mapPullbackAdj f : Over.map f ⊣ Over.pullback f)

/- The continuous presentations associated to the adjoint slice functors are adjoint. -/
#check
  (CategoryTheory.Adjunction.sheafPushforwardContinuous
      (Over.mapPullbackAdj f)
      ((fppfTopology S).over Y) ((fppfTopology S).over X) :
    CategoryTheory.Over.Site.inverseImage (fppfTopology S) f ⊣
      (Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        ((fppfTopology S).over X) ((fppfTopology S).over Y))

/- The cocontinuous and continuous-right-adjoint presentations of direct image agree. -/
#check
  (CategoryTheory.Over.Site.DirectImage.pullbackPresentation (fppfTopology S) f :
    CategoryTheory.Over.Site.directImage (fppfTopology S) f ≅
      (Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        ((fppfTopology S).over X) ((fppfTopology S).over Y))

/- Inverse image is computed by postcomposition on the slice object. -/
#check
  (CategoryTheory.Over.Site.InverseImage.obj_eq (fppfTopology S) f :
    ∀ (G : Sheaf ((fppfTopology S).over X) (Type (u + 1))) (U : Over Y),
      (((CategoryTheory.Over.Site.inverseImage (fppfTopology S) f).obj G).obj.obj (op U)) =
        G.obj.obj (op ((Over.map f).obj U)))

/- Direct image is canonically computed by evaluation on the pullback slice object. -/
#check
  (CategoryTheory.Over.Site.DirectImage.objIso (fppfTopology S) f :
    ∀ (F : Sheaf ((fppfTopology S).over Y) (Type (u + 1))) (U : Over X),
      (((CategoryTheory.Over.Site.directImage (fppfTopology S) f).obj F).obj.obj (op U)) ≅
        F.obj.obj (op ((Over.pullback f).obj U)))

/- The continuous direct-image presentation has the corresponding objectwise formula. -/
#check
  (CategoryTheory.Functor.sheafPushforwardContinuousObjObjIso
      (Over.pullback f) (Type (u + 1)) :
    ∀ (F : Sheaf ((fppfTopology S).over Y) (Type (u + 1))) (U : Over X),
      ((((Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        ((fppfTopology S).over X) ((fppfTopology S).over Y)).obj F).obj.obj (op U)) ≅
        F.obj.obj (op ((Over.pullback f).obj U)))

/- The concrete lower-shriek functor is left adjoint to inverse image. -/
#check
  (CategoryTheory.Over.Site.LowerShriek.adjunction.{u + 1, u + 1, u + 1}
      (fppfTopology S) f :
    CategoryTheory.Over.Site.lowerShriek.{u + 1, u + 1, u + 1} (fppfTopology S) f ⊣
      CategoryTheory.Over.Site.inverseImage.{u + 1, u + 1, u + 1} (fppfTopology S) f)

/- Lower shriek preserves pullbacks and equalizers. -/
#check
  (lowerShriek_preservesPullbacks f :
    PreservesLimitsOfShape WalkingCospan
      (CategoryTheory.Over.Site.lowerShriek.{u + 1, u + 1, u + 1} (fppfTopology S) f))

#check
  (lowerShriek_preservesEqualizers f :
    PreservesLimitsOfShape WalkingParallelPair
      (CategoryTheory.Over.Site.lowerShriek.{u + 1, u + 1, u + 1} (fppfTopology S) f))

end

end AlgebraicGeometry
