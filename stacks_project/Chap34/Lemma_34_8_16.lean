/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Big
import StacksCheckRecall

/-!
# Lemma 34.8.16

This chapter file records the source-facing big ph topos construction and
retains the topology-parametric spelling used by the following chapter item.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped MorphismOfTopoiIn

noncomputable section

universe u w

namespace AlgebraicGeometry

/-- The topology-parametric slice morphism of topoi retained for compatibility. -/
noncomputable abbrev bigPhMorphismOfTopoi
    (Jph : GrothendieckTopology Scheme.{u}) {S T : Scheme.{u}} (f : T ⟶ S)
    [Functor.IsContinuous (Over.map f) (Jph.over T) (Jph.over S)]
    [Functor.IsCocontinuous (Over.map f) (Jph.over T) (Jph.over S)]
    [HasWeakSheafify (Jph.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (Over.map f).op.HasLeftKanExtension P]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w,
      (Over.map f).op.HasPointwiseRightKanExtension P] :
    MorphismOfTopoiIn (Jph.over S) (Jph.over T) where
  inverseImageFunctor :=
    LeftExactFunctor.of
      ((Over.map f).sheafPushforwardContinuous (Type w) (Jph.over T) (Jph.over S))
  pushforward :=
    (Over.map f).sheafPushforwardCocontinuous (Type w) (Jph.over T) (Jph.over S)
  adjunction :=
    (Over.map f).sheafAdjunctionCocontinuous (Type w) (Jph.over T) (Jph.over S)

section

variable {S T : Scheme.{u}} (f : T ⟶ S)

/- Lemma 34.8.16 (1): a scheme morphism induces a morphism between its big ph topoi. -/
@[stacks 0DBR] #check
  (AlgebraicGeometry.Scheme.Ph.Big.morphismOfTopoi :
    ∀ {S T : Scheme.{u}} (f : T ⟶ S),
      MorphismOfTopoiIn (Scheme.bigPhSite S) (Scheme.bigPhSite T))

/- Companion check: postcomposition is cocontinuous on the big ph sites. -/
#check
  (AlgebraicGeometry.Scheme.Ph.Big.map_isCocontinuous f :
    Functor.IsCocontinuous (AlgebraicGeometry.Scheme.Ph.Big.map f)
      (Scheme.bigPhSite T) (Scheme.bigPhSite S))

/- Companion check: postcomposition is continuous on the big ph sites. -/
#check
  (AlgebraicGeometry.Scheme.Ph.Big.map_isContinuous f :
    Functor.IsContinuous (AlgebraicGeometry.Scheme.Ph.Big.map f)
      (Scheme.bigPhSite T) (Scheme.bigPhSite S))

/- Companion check: pullback is the continuous right adjoint of postcomposition. -/
#check
  (AlgebraicGeometry.Scheme.Ph.Big.mapPullbackAdjunction f :
    AlgebraicGeometry.Scheme.Ph.Big.map f ⊣
      AlgebraicGeometry.Scheme.Ph.Big.pullback f)

#check
  (AlgebraicGeometry.Scheme.Ph.Big.pullback_isContinuous f :
    Functor.IsContinuous (AlgebraicGeometry.Scheme.Ph.Big.pullback f)
      (Scheme.bigPhSite S) (Scheme.bigPhSite T))

/- Companion check: the two direct-image presentations are canonically isomorphic. -/
#check
  (AlgebraicGeometry.Scheme.Ph.Big.directImageIsoPullbackPresentation f :
    AlgebraicGeometry.Scheme.Ph.Big.directImage f ≅
      AlgebraicGeometry.Scheme.Ph.Big.continuousDirectImage f)

/- Companion check: the bundled inverse image is the canonical inverse-image functor. -/
#check
  (AlgebraicGeometry.Scheme.Ph.Big.morphismOfTopoi_inverseImage f :
    (AlgebraicGeometry.Scheme.Ph.Big.morphismOfTopoi f)⁻¹ =
      AlgebraicGeometry.Scheme.Ph.Big.inverseImage f)

/- Companion check: inverse image evaluates on the postcomposed slice object. -/
#check
  (AlgebraicGeometry.Scheme.Ph.Big.inverseImage_obj_obj f :
    ∀ (G : Sheaf (Scheme.bigPhSite S) (Type (u + 1))) (U : Over T),
      (((AlgebraicGeometry.Scheme.Ph.Big.inverseImage f).obj G).obj.obj (op U)) =
        G.obj.obj (op ((AlgebraicGeometry.Scheme.Ph.Big.map f).obj U)))

/- Companion check: the bundled direct image is the canonical direct-image functor. -/
#check
  (AlgebraicGeometry.Scheme.Ph.Big.morphismOfTopoi_pushforward f :
    (AlgebraicGeometry.Scheme.Ph.Big.morphismOfTopoi f).pushforward =
      AlgebraicGeometry.Scheme.Ph.Big.directImage f)

/- Companion check: direct image evaluates on the pullback slice object. -/
#check
  (AlgebraicGeometry.Scheme.Ph.Big.directImage_obj_obj f :
    ∀ (F : Sheaf (Scheme.bigPhSite T) (Type (u + 1))) (U : Over S),
      (((AlgebraicGeometry.Scheme.Ph.Big.directImage f).obj F).obj.obj (op U)) =
        F.obj.obj (op ((AlgebraicGeometry.Scheme.Ph.Big.pullback f).obj U)))

/- Companion check: lower shriek is left adjoint to inverse image. -/
#check
  (AlgebraicGeometry.Scheme.Ph.Big.lowerShriekAdjunction f :
    AlgebraicGeometry.Scheme.Ph.Big.lowerShriek f ⊣
      AlgebraicGeometry.Scheme.Ph.Big.inverseImage f)

/- Companion check: lower shriek preserves fibre products. -/
#check
  (AlgebraicGeometry.Scheme.Ph.Big.lowerShriek_preservesPullbacks f :
    PreservesLimitsOfShape WalkingCospan
      (AlgebraicGeometry.Scheme.Ph.Big.lowerShriek f))

/- Companion check: lower shriek preserves equalizers. -/
#check
  (AlgebraicGeometry.Scheme.Ph.Big.lowerShriek_preservesEqualizers f :
    PreservesLimitsOfShape WalkingParallelPair
      (AlgebraicGeometry.Scheme.Ph.Big.lowerShriek f))

end

end AlgebraicGeometry
