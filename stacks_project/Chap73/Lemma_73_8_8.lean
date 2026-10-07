module

public import stacks_project.Chap73.Lemma_73_8_8_Site
public import stacks_project.Chap73.Lemma_73_8_8_Big
import StacksCheckRecall

/-!
# Lemma 73.8.8

A morphism of algebraic spaces over a scheme induces a morphism of big ph topoi.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Ph.Big
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry

/- Lemma 73.8.8 -/
@[stacks 0DFN] #check
  (morphismOfTopoi :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
      (Y ⟶ X) → MorphismOfTopoiIn (bigPhSite X) (bigPhSite Y))

section

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)

/- Companion check: postcomposition is cocontinuous on the big ph sites. -/
#check
  (map_isCocontinuous f :
    Functor.IsCocontinuous (map f) (bigPhSite Y) (bigPhSite X))

/- Companion check: postcomposition is continuous on the big ph sites. -/
#check
  (map_isContinuous f :
    Functor.IsContinuous (map f) (bigPhSite Y) (bigPhSite X))

/- Companion check: pullback is the continuous right adjoint of postcomposition. -/
#check
  (mapPullbackAdjunction f : map f ⊣ Ph.Big.pullback f)

#check
  (pullback_isContinuous f :
    Functor.IsContinuous (Ph.Big.pullback f) (bigPhSite X) (bigPhSite Y))

/- Companion check: the two direct-image presentations are canonically isomorphic. -/
#check
  (directImageIsoPullbackPresentation f :
    directImage f ≅ continuousDirectImage f)

/- Companion check: the bundled inverse image is the canonical inverse-image functor. -/
#check
  (morphismOfTopoi_inverseImage f :
    (morphismOfTopoi f)⁻¹ = inverseImage f)

/- Companion check: inverse image evaluates on the postcomposed slice object. -/
#check
  (inverseImage_obj_obj f :
    ∀ (G : Sheaf (bigPhSite X) (Type (u + 1))) (U : Over Y),
      (((inverseImage f).obj G).obj.obj (op U)) =
        G.obj.obj (op ((map f).obj U)))

/- Companion check: the bundled direct image is the canonical direct-image functor. -/
#check
  (morphismOfTopoi_pushforward f :
    (morphismOfTopoi f).pushforward = directImage f)

/- Companion check: direct image is canonically isomorphic to evaluation on the
pullback slice object. -/
#check
  (directImage_objObjIso f :
    ∀ (F : Sheaf (bigPhSite Y) (Type (u + 1))) (U : Over X),
      (((directImage f).obj F).obj.obj (op U)) ≅
        F.obj.obj (op ((Ph.Big.pullback f).obj U)))

/- Companion check: the continuous direct-image presentation evaluates on the
pullback slice object. -/
#check
  (continuousDirectImage_obj_obj f :
    ∀ (F : Sheaf (bigPhSite Y) (Type (u + 1))) (U : Over X),
      (((continuousDirectImage f).obj F).obj.obj (op U)) =
        F.obj.obj (op ((Ph.Big.pullback f).obj U)))

/- Companion check: lower shriek is left adjoint to inverse image. -/
#check
  (lowerShriekAdjunction f : lowerShriek f ⊣ inverseImage f)

/- Companion check: lower shriek preserves fibre products. -/
#check
  (lowerShriek_preservesPullbacks f :
    PreservesLimitsOfShape WalkingCospan (lowerShriek f))

/- Companion check: lower shriek preserves equalizers. -/
#check
  (lowerShriek_preservesEqualizers f :
    PreservesLimitsOfShape WalkingParallelPair (lowerShriek f))

end

end AlgebraicGeometry
