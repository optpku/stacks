module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.SmallToBig
public import ReasLib.CategoryTheory.Sites.Over.BaseChange

/-!
# Base change for Zariski topoi

Cartesian squares of schemes induce the mixed small-to-big base-change comparison between
Zariski direct and inverse images.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Zariski.BaseChange

variable {S S' T T' : Scheme.{u}}

/-- The canonical comparison between the two pullbacks of a small Zariski object around a
cartesian square. -/
private noncomputable def pullbackRelocalizationIsoApp
    (f : T ⟶ S) (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T)
    (sq : IsPullback g' f' f g) (U : S'.smallZariskiSite) :
    (smallZariskiPullback f' ⋙ Zariski.SmallToBig.relocalizationFunctor g').obj U ≅
      (Zariski.SmallToBig.relocalizationFunctor g ⋙ Zariski.Big.pullback f).obj U :=
  let inner : IsPullback
      (pullback.snd U.hom f') (pullback.fst U.hom f') f' U.hom :=
    (IsPullback.of_hasPullback U.hom f').flip
  let outer : IsPullback
      (pullback.snd U.hom f' ≫ g') (pullback.fst U.hom f') f (U.hom ≫ g) :=
    inner.paste_horiz sq
  let chosen : IsPullback
      (pullback.snd (U.hom ≫ g) f) (pullback.fst (U.hom ≫ g) f)
        f (U.hom ≫ g) :=
    (IsPullback.of_hasPullback (U.hom ≫ g) f).flip
  Over.isoMk (outer.isoIsPullback T U.left chosen)
    (outer.isoIsPullback_hom_fst T U.left chosen)

/-- Relocalization sends a small Zariski object to its structural morphism followed by the
base morphism. -/
@[simp]
private theorem relocalizationFunctor_obj_hom
    (g : S' ⟶ S) (U : S'.smallZariskiSite) :
    ((Zariski.SmallToBig.relocalizationFunctor g).obj U).hom = U.hom ≫ g := rfl

/-- The comparison of pullbacks around a cartesian square commutes with the projection to the
small Zariski object. -/
@[reassoc]
private theorem pullbackRelocalizationIsoApp_hom_fst
    (f : T ⟶ S) (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T)
    (sq : IsPullback g' f' f g) (U : S'.smallZariskiSite) :
    (pullbackRelocalizationIsoApp f g f' g' sq U).hom.left ≫
        pullback.fst ((Zariski.SmallToBig.relocalizationFunctor g).obj U).hom f =
      pullback.fst U.hom f' := by
  dsimp [pullbackRelocalizationIsoApp]
  apply IsPullback.isoIsPullback_hom_snd

/-- The comparison of pullbacks around a cartesian square commutes with the projection to the
upper-right scheme. -/
@[reassoc]
private theorem pullbackRelocalizationIsoApp_hom_snd
    (f : T ⟶ S) (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T)
    (sq : IsPullback g' f' f g) (U : S'.smallZariskiSite) :
    (pullbackRelocalizationIsoApp f g f' g' sq U).hom.left ≫
        pullback.snd ((Zariski.SmallToBig.relocalizationFunctor g).obj U).hom f =
      pullback.snd U.hom f' ≫ g' := by
  dsimp [pullbackRelocalizationIsoApp]
  apply IsPullback.isoIsPullback_hom_fst

/-- The map on the small pullback-relocalization composite commutes with the first pullback
projection. -/
@[reassoc]
private theorem smallPullbackRelocalization_map_fst
    (f' : T' ⟶ S') (g' : T' ⟶ T) {U V : S'.smallZariskiSite} (φ : U ⟶ V) :
    ((smallZariskiPullback f' ⋙ Zariski.SmallToBig.relocalizationFunctor g').map φ).left ≫
        pullback.fst V.hom f' =
      pullback.fst U.hom f' ≫ φ.left := by
  change ((smallZariskiPullback f').map φ).left ≫ pullback.fst V.hom f' = _
  erw [MorphismProperty.Over.pullback_map_left, pullback.lift_fst]
  rfl

/-- The map on the small pullback-relocalization composite commutes with the second pullback
projection. -/
@[reassoc]
private theorem smallPullbackRelocalization_map_snd
    (f' : T' ⟶ S') (g' : T' ⟶ T) {U V : S'.smallZariskiSite} (φ : U ⟶ V) :
    ((smallZariskiPullback f' ⋙ Zariski.SmallToBig.relocalizationFunctor g').map φ).left ≫
        pullback.snd V.hom f' =
      pullback.snd U.hom f' := by
  change ((smallZariskiPullback f').map φ).left ≫ pullback.snd V.hom f' = _
  erw [MorphismProperty.Over.pullback_map_left, pullback.lift_snd]
  rfl

/-- Relocalization preserves the underlying map of a small Zariski morphism. -/
private theorem relocalizationFunctor_map_left
    (g : S' ⟶ S) {U V : S'.smallZariskiSite} (φ : U ⟶ V) :
    ((Zariski.SmallToBig.relocalizationFunctor g).map φ).left = φ.left := rfl

/-- The map on the relocalization-big-pullback composite is the canonical map between chosen
pullbacks. -/
private theorem relocalizationBigPullback_map_left
    (f : T ⟶ S) (g : S' ⟶ S) {U V : S'.smallZariskiSite} (φ : U ⟶ V) :
    ((Zariski.SmallToBig.relocalizationFunctor g ⋙ Zariski.Big.pullback f).map φ).left =
      pullback.lift
        (pullback.fst ((Zariski.SmallToBig.relocalizationFunctor g).obj U).hom f ≫
          ((Zariski.SmallToBig.relocalizationFunctor g).map φ).left)
        (pullback.snd ((Zariski.SmallToBig.relocalizationFunctor g).obj U).hom f) (by
          rw [Category.assoc, Over.w, pullback.condition]) := by
  change ((Over.pullback f).map ((Zariski.SmallToBig.relocalizationFunctor g).map φ)).left = _
  exact Over.pullback_map_left f ((Zariski.SmallToBig.relocalizationFunctor g).obj U)

/-- The map on the relocalization-big-pullback composite commutes with the first pullback
projection. -/
@[reassoc]
private theorem relocalizationBigPullback_map_fst
    (f : T ⟶ S) (g : S' ⟶ S) {U V : S'.smallZariskiSite} (φ : U ⟶ V) :
    ((Zariski.SmallToBig.relocalizationFunctor g ⋙ Zariski.Big.pullback f).map φ).left ≫
        pullback.fst ((Zariski.SmallToBig.relocalizationFunctor g).obj V).hom f =
      pullback.fst ((Zariski.SmallToBig.relocalizationFunctor g).obj U).hom f ≫ φ.left := by
  rw [relocalizationBigPullback_map_left]
  erw [pullback.lift_fst]
  rw [relocalizationFunctor_map_left]
  rfl

/-- The map on the relocalization-big-pullback composite commutes with the second pullback
projection. -/
@[reassoc]
private theorem relocalizationBigPullback_map_snd
    (f : T ⟶ S) (g : S' ⟶ S) {U V : S'.smallZariskiSite} (φ : U ⟶ V) :
    ((Zariski.SmallToBig.relocalizationFunctor g ⋙ Zariski.Big.pullback f).map φ).left ≫
        pullback.snd ((Zariski.SmallToBig.relocalizationFunctor g).obj V).hom f =
      pullback.snd ((Zariski.SmallToBig.relocalizationFunctor g).obj U).hom f := by
  rw [relocalizationBigPullback_map_left]
  erw [pullback.lift_snd]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Pulling a small Zariski object around a cartesian square agrees with first viewing it on the
big Zariski site and then pulling it back. -/
private noncomputable def pullbackRelocalizationIso
    (f : T ⟶ S) (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T)
    (sq : IsPullback g' f' f g) :
    smallZariskiPullback f' ⋙ Zariski.SmallToBig.relocalizationFunctor g' ≅
      Zariski.SmallToBig.relocalizationFunctor g ⋙ Zariski.Big.pullback f :=
  NatIso.ofComponents (pullbackRelocalizationIsoApp f g f' g' sq)
    (fun {U V} φ ↦ by
      ext
      apply pullback.hom_ext
      · simp only [Over.comp_left]
        rw [Category.assoc, pullbackRelocalizationIsoApp_hom_fst]
        slice_lhs 1 2 =>
          erw [smallPullbackRelocalization_map_fst]
        rw [Category.assoc, relocalizationBigPullback_map_fst,
          ← Category.assoc, pullbackRelocalizationIsoApp_hom_fst]
      · simp only [Over.comp_left]
        rw [Category.assoc, pullbackRelocalizationIsoApp_hom_snd,
          ← Category.assoc]
        slice_lhs 1 2 =>
          erw [smallPullbackRelocalization_map_snd]
        rw [Category.assoc, relocalizationBigPullback_map_snd,
          pullbackRelocalizationIsoApp_hom_snd])

/-- The canonical mixed small-to-big Beck-Chevalley comparison for a cartesian square of
schemes. -/
@[no_expose]
noncomputable def smallToBigComparison
    (f : T ⟶ S) (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T)
    (sq : IsPullback g' f' f g) :
    (Zariski.Big.morphismOfTopoi f) _* ⋙
        (Zariski.SmallToBig.morphismOfTopoi g)⁻¹ ⟶
      (Zariski.SmallToBig.morphismOfTopoi g')⁻¹ ⋙
        (Zariski.SmallToBig.smallMorphism f') _* :=
  -- Local instance justification (instance diamond): the cartesian-square comparison must pin continuity of the relocalization-pullback composite because both component and composite continuity instances are available.
  letI : Functor.IsContinuous
      (Zariski.SmallToBig.relocalizationFunctor g ⋙ Zariski.Big.pullback f)
      S'.smallZariskiTopology T.bigZariskiTopology :=
    Functor.isContinuous_comp
      (Zariski.SmallToBig.relocalizationFunctor g) (Zariski.Big.pullback f)
      S'.smallZariskiTopology S.bigZariskiTopology T.bigZariskiTopology
  (Functor.isoWhiskerRight (Zariski.Big.directImageIsoPullbackPresentation f)
      (Zariski.SmallToBig.inverseImage g) ≪≫
    (Functor.sheafPushforwardContinuousComp'
        (pullbackRelocalizationIso f g f' g' sq) (Type (u + 1))
        S'.smallZariskiTopology T'.smallZariskiTopology T.bigZariskiTopology ≪≫
      (Functor.sheafPushforwardContinuousComp
        (Zariski.SmallToBig.relocalizationFunctor g)
        (Zariski.Big.pullback f) (Type (u + 1))
        S'.smallZariskiTopology S.bigZariskiTopology T.bigZariskiTopology).symm).symm).hom

/-- The mixed small-to-big Beck-Chevalley comparison for a cartesian square is invertible. -/
noncomputable instance smallToBigComparison_isIso
    (f : T ⟶ S) (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T)
    (sq : IsPullback g' f' f g) :
    IsIso (smallToBigComparison f g f' g' sq) := sorry

end AlgebraicGeometry.Scheme.Zariski.BaseChange
