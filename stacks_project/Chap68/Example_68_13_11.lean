module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ProfiniteTranslation

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ProfiniteTranslation

universe u

/- Example 68.13.11: The projection from the affine profinite scheme to its
translation quotient does not factor through a field-valued point. -/
@[stacks 0H2Y] #check
  (AlgebraicGeometry.AlgebraicSpace.ProfiniteTranslation.not_exists_fieldValued_factor :
    ∀ (k : Type u) [Field k] (G : ProfiniteGrp.{u}) [Infinite G],
      ¬ ∃ (p : FieldValuedPoint (X k G)) (φ : ofOver (YOver k G) ⟶ ofOver p.overObj),
        φ ≫ p.hom = q k G)

#check (AlgebraicGeometry.isAffine_Spec :
  ∀ (R : CommRingCat.{u}), AlgebraicGeometry.IsAffine (Spec R))

#check (AlgebraicGeometry.AlgebraicSpace.ProfiniteTranslation.instIsReduced_Y :
  ∀ (k : Type u) [Field k] (G : ProfiniteGrp.{u}),
    AlgebraicGeometry.IsReduced (YOver k G).left)

#check (LocallyConstant.instKrullDimLE_zero :
  ∀ (T K : Type u) [TopologicalSpace T] [Field K],
    Ring.KrullDimLE 0 (LocallyConstant T K))

#check (AlgebraicGeometry.AlgebraicSpace.ProfiniteTranslation.points_eq_singleton :
  ∀ (k : Type u) [Field k] (G : ProfiniteGrp.{u}) [Infinite G],
    (Set.univ : Set (Points (X k G))) = {Points.mk (x k G)})

#check (AlgebraicGeometry.AlgebraicSpace.ProfiniteTranslation.isSplitMono_x :
  ∀ (k : Type u) [Field k] (G : ProfiniteGrp.{u}), IsSplitMono (x k G).hom)

#check (AlgebraicGeometry.AlgebraicSpace.ProfiniteTranslation.instMono_x :
  ∀ (k : Type u) [Field k] (G : ProfiniteGrp.{u}), Mono (x k G).hom)

#check (AlgebraicGeometry.AlgebraicSpace.ProfiniteTranslation.isPullback_orbit :
  ∀ (k : Type u) [Field k] (G : ProfiniteGrp.{u}) [Infinite G],
    IsPullback (ofOverMap (orbit k G)) (ofOverMap (ΓToBase k G)) (q k G) (x k G).hom)

#check (AlgebraicGeometry.AlgebraicSpace.ProfiniteTranslation.not_exists_section_orbit :
  ∀ (k : Type u) [Field k] (G : ProfiniteGrp.{u}) [Infinite G],
    ¬ ∃ s : YOver k G ⟶ ΓOver k G, s ≫ orbit k G = 𝟙 (YOver k G))

#check (AlgebraicGeometry.AlgebraicSpace.ProfiniteTranslation.not_isLocallyNoetherian_X :
  ∀ (k : Type u) [Field k] (G : ProfiniteGrp.{u}) [Infinite G],
    ¬ IsLocallyNoetherian (X k G))

#check (AlgebraicGeometry.AlgebraicSpace.ProfiniteTranslation.not_isDecent_X :
  ∀ (k : Type u) [Field k] (G : ProfiniteGrp.{u}) [Infinite G], ¬ IsDecent (X k G))
