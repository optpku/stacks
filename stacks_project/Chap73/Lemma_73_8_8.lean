module

public import stacks_project.Chap73.Lemma_73_8_8_Site
public import stacks_project.Chap73.Lemma_73_8_8_Big
public import ReasLib.CategoryTheory.Limits.Over.FiniteLimits
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
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)

/- Lemma 73.8.8 -/
@[stacks 0DFN] #check
  (CategoryTheory.Over.Site.morphismOfTopoi.{u + 1, u + 1, u + 1} (phTopology S) f :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, u + 1}
      (bigPhSite X) (bigPhSite Y))

/- Companion check: postcomposition is cocontinuous on the big ph sites. -/
#check (inferInstance :
  Functor.IsCocontinuous (Over.map f) (bigPhSite Y) (bigPhSite X))

/- Companion check: postcomposition is continuous on the big ph sites. -/
#check (inferInstance :
  Functor.IsContinuous (Over.map f) (bigPhSite Y) (bigPhSite X))

/- Companion check: pullback is the continuous right adjoint of postcomposition. -/
#check (Over.Site.mapPullbackAdjunction f :
  Over.map f ⊣ Over.pullback f)

#check (inferInstance :
  Functor.IsContinuous (Over.pullback f) (bigPhSite X) (bigPhSite Y))

/- Companion check: the two direct-image presentations are canonically isomorphic. -/
#check (Over.Site.DirectImage.pullbackPresentation.{u + 1, u + 1, u + 1} (phTopology S) f :
  (Over.Site.directImage.{u + 1, u + 1, u + 1} (phTopology S) f :
    Sheaf (bigPhSite Y) (Type (u + 1)) ⥤ Sheaf (bigPhSite X) (Type (u + 1))) ≅
      (Over.pullback f).sheafPushforwardContinuous
        (Type (u + 1)) (bigPhSite X) (bigPhSite Y))

/- Companion check: inverse image evaluates on the postcomposed slice object. -/
#check (Over.Site.InverseImage.obj_eq (phTopology S) f :
  ∀ (G : Sheaf (bigPhSite X) (Type (u + 1))) (U : Over Y),
    ((Over.Site.inverseImage.{u + 1, u + 1, u + 1} (phTopology S) f).obj G).obj.obj (op U) =
      G.obj.obj (op ((Over.map f).obj U)))

/- Companion check: direct image evaluates on the pullback slice object. -/
#check (Over.Site.DirectImage.objIso.{u + 1, u + 1, u + 1} (phTopology S) f :
  ∀ (F : Sheaf (bigPhSite Y) (Type (u + 1))) (U : Over X),
    ((Over.Site.directImage.{u + 1, u + 1, u + 1} (phTopology S) f).obj F).obj.obj (op U) ≅
      F.obj.obj (op ((Over.pullback f).obj U)))

/- Companion check: lower shriek is left adjoint to the canonical inverse image. -/
#check (Over.Site.LowerShriek.adjunction.{u + 1, u + 1, u + 1} (phTopology S) f :
  (Over.Site.lowerShriek.{u + 1, u + 1, u + 1} (phTopology S) f :
    Sheaf (bigPhSite Y) (Type (u + 1)) ⥤ Sheaf (bigPhSite X) (Type (u + 1))) ⊣
      Over.Site.inverseImage.{u + 1, u + 1, u + 1} (phTopology S) f)

/- Companion check: lower shriek preserves fibre products. -/
#check (Over.Site.LowerShriek.Pullbacks.preservesPullbacks.{u + 1, u + 1, u + 1} (phTopology S) f :
  PreservesLimitsOfShape WalkingCospan
    (Over.Site.lowerShriek.{u + 1, u + 1, u + 1} (phTopology S) f :
      Sheaf (bigPhSite Y) (Type (u + 1)) ⥤ Sheaf (bigPhSite X) (Type (u + 1))))

/- Companion check: lower shriek preserves equalizers. -/
#check (Over.Site.LowerShriek.Pullbacks.preservesEqualizers.{u + 1, u + 1, u + 1} (phTopology S) f :
  PreservesLimitsOfShape WalkingParallelPair
    (Over.Site.lowerShriek.{u + 1, u + 1, u + 1} (phTopology S) f :
      Sheaf (bigPhSite Y) (Type (u + 1)) ⥤ Sheaf (bigPhSite X) (Type (u + 1))))

end AlgebraicGeometry
