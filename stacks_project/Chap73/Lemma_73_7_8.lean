module

import StacksCheckRecall
public import stacks_project.Chap73.Lemma_73_7_8_Topology
public import stacks_project.Chap73.Lemma_73_7_8_Big

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
  (morphismOfTopoi f :
    MorphismOfTopoiIn ((fppfTopology S).over X) ((fppfTopology S).over Y))

/- Postcomposition and pullback are the functors between the big fppf slices. -/
#check (map f : Over Y ⥤ Over X)

#check (Fppf.Big.pullback f : Over X ⥤ Over Y)

/- Postcomposition is cocontinuous and continuous, pullback is continuous, and
the two functors form the canonical adjunction. -/
#check
  (inferInstance :
    Functor.IsCocontinuous (map f)
      ((fppfTopology S).over Y) ((fppfTopology S).over X))

#check
  (inferInstance :
    Functor.IsContinuous (map f)
      ((fppfTopology S).over Y) ((fppfTopology S).over X))

#check
  (inferInstance :
    Functor.IsContinuous (pullback f)
      ((fppfTopology S).over X) ((fppfTopology S).over Y))

#check
  (mapPullbackAdjunction f : map f ⊣ pullback f)

/- The continuous presentations associated to the adjoint slice functors are adjoint. -/
#check
  (CategoryTheory.Adjunction.sheafPushforwardContinuous
      (mapPullbackAdjunction f)
      ((fppfTopology S).over Y) ((fppfTopology S).over X) :
    inverseImage f ⊣ continuousDirectImage f)

/- The cocontinuous and continuous-right-adjoint presentations of direct image agree. -/
#check
  (directImageIsoPullbackPresentation f :
    directImage f ≅ continuousDirectImage f)

/- Inverse image is computed by postcomposition on the slice object. -/
#check
  (inverseImage_obj_obj f :
    ∀ (G : Sheaf ((fppfTopology S).over X) (Type (u + 1))) (U : Over Y),
      (((inverseImage f).obj G).obj.obj (op U)) =
        G.obj.obj (op ((map f).obj U)))

/- Direct image is canonically computed by evaluation on the pullback slice object. -/
#check
  (directImage_objObjIso f :
    ∀ (F : Sheaf ((fppfTopology S).over Y) (Type (u + 1))) (U : Over X),
      (((directImage f).obj F).obj.obj (op U)) ≅
        F.obj.obj (op ((Fppf.Big.pullback f).obj U)))

/- The continuous direct-image presentation has the corresponding objectwise formula. -/
#check
  (continuousDirectImage_obj_obj f :
    ∀ (F : Sheaf ((fppfTopology S).over Y) (Type (u + 1))) (U : Over X),
      (((continuousDirectImage f).obj F).obj.obj (op U)) =
        F.obj.obj (op ((Fppf.Big.pullback f).obj U)))

/- The concrete lower-shriek functor is left adjoint to inverse image. -/
#check
  (lowerShriekAdjunction f : lowerShriek f ⊣ inverseImage f)

/- Lower shriek preserves pullbacks and equalizers. -/
#check
  (lowerShriek_preservesPullbacks f :
    PreservesLimitsOfShape WalkingCospan (lowerShriek f))

#check
  (lowerShriek_preservesEqualizers f :
    PreservesLimitsOfShape WalkingParallelPair (lowerShriek f))

end

end AlgebraicGeometry
