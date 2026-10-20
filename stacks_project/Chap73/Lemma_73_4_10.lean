/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.BigTopos

/-!
# Lemma 73.4.10

A morphism of algebraic spaces over a scheme induces a morphism of big étale
topoi.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.Big
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)

/- Lemma 73.4.10 -/
@[stacks 0DF5] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.Big.morphismOfTopoi f :
    MorphismOfTopoiIn (overEtaleTopology X) (overEtaleTopology Y))

/- Postcomposition and pullback are the functors between the big étale slices. -/
#check (Over.map f : Over Y ⥤ Over X)

#check (Over.pullback f : Over X ⥤ Over Y)

/- Postcomposition is cocontinuous and continuous, pullback is continuous, and
the two functors form the canonical adjunction. -/
#check
  (inferInstance :
    Functor.IsCocontinuous (Over.map f)
      (overEtaleTopology Y) (overEtaleTopology X))

#check
  (inferInstance :
    Functor.IsContinuous (Over.map f)
      (overEtaleTopology Y) (overEtaleTopology X))

#check
  (inferInstance :
    Functor.IsContinuous (Over.pullback f)
      (overEtaleTopology X) (overEtaleTopology Y))

#check
  (Over.mapPullbackAdj f : Over.map f ⊣ Over.pullback f)

/- The cocontinuous and continuous-right-adjoint presentations of direct image agree. -/
#check
  (directImageIsoPullbackPresentation f :
    directImage f ≅ continuousDirectImage f)

/- The bundled inverse image is the canonical inverse-image functor. -/
#check
  (morphismOfTopoi_inverseImage f :
    (morphismOfTopoi f)⁻¹ = inverseImage f)

/- Inverse image is computed by postcomposition on the slice object. -/
#check
  (inverseImage_obj_obj f :
    ∀ (G : Sheaf (overEtaleTopology X) (Type (u + 1))) (U : Over Y),
      (((inverseImage f).obj G).obj.obj (op U)) =
        G.obj.obj (op ((Over.map f).obj U)))

/- The bundled inverse image has the corresponding objectwise identification. -/
#check
  (morphismOfTopoi_inverseImage_objObjIso f :
    ∀ (G : Sheaf (overEtaleTopology X) (Type (u + 1))) (U : Over Y),
      (((morphismOfTopoi f)⁻¹).obj G).obj.obj (op U) ≅
        G.obj.obj (op ((Over.map f).obj U)))

/- The bundled direct image is the canonical direct-image functor. -/
#check
  (morphismOfTopoi_pushforward f :
    (morphismOfTopoi f).pushforward = directImage f)

/- Direct image is canonically computed by evaluation on the pullback slice object. -/
#check
  (directImage_objObjIso f :
    ∀ (F : Sheaf (overEtaleTopology Y) (Type (u + 1))) (U : Over X),
      (((directImage f).obj F).obj.obj (op U)) ≅
        F.obj.obj (op ((Over.pullback f).obj U)))

/- The bundled direct image has the corresponding objectwise identification. -/
#check
  (morphismOfTopoi_pushforward_objObjIso f :
    ∀ (F : Sheaf (overEtaleTopology Y) (Type (u + 1))) (U : Over X),
      (((morphismOfTopoi f).pushforward.obj F).obj.obj (op U)) ≅
        F.obj.obj (op ((Over.pullback f).obj U)))

/- The continuous direct-image presentation has the corresponding objectwise formula. -/
#check
  (continuousDirectImage_obj_obj f :
    ∀ (F : Sheaf (overEtaleTopology Y) (Type (u + 1))) (U : Over X),
      (((continuousDirectImage f).obj F).obj.obj (op U)) =
        F.obj.obj (op ((Over.pullback f).obj U)))

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
