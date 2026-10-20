module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Sites.Over.Adjunction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Small-étale to big h pushforward comparisons

Canonical comparison morphism of topoi `a_X = π_X ∘ ε_X` from the small étale
topos of a scheme to its big h topos, together with the Type-valued mate
identifying small étale direct images with big h direct images after `a⁻¹`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale.SmallToBig
open scoped MorphismOfTopoiIn

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.HComparison

variable {X Y : Scheme.{u}}

/-- Relocalization from the small étale site of `X` is continuous into the big h site. -/
instance relocalizationFunctor_isContinuous_h (X : Scheme.{u}) :
    (relocalizationFunctor (𝟙 X)).IsContinuous X.smallEtaleTopology (H.Big.site X) :=
  @Functor.isContinuous_comp' _ _ _ _ _ _ _ _ _
    (Functor.rightUnitor (relocalizationFunctor (𝟙 X)))
    X.smallEtaleTopology (X.overGrothendieckTopology @Etale) (H.Big.site X)
    inferInstance (identity_isMorphismOfSites X).toIsContinuous

/-- The composite `smallEtalePullback f ⋙ relocalizationFunctor (𝟙 X)` is continuous from the
small étale topology of `Y` to the big h topology of `X`. -/
instance isContinuous_smallEtalePullback_comp_relocalization_h {f : X ⟶ Y} :
    Functor.IsContinuous (smallEtalePullback f ⋙ relocalizationFunctor (𝟙 X))
      Y.smallEtaleTopology (H.Big.site X) :=
  Functor.isContinuous_comp (smallEtalePullback f) (relocalizationFunctor (𝟙 X))
    Y.smallEtaleTopology X.smallEtaleTopology (H.Big.site X)

/-- Continuous sheaf pushforward along `Over.pullback f` on big h sites is a right adjoint. -/
instance isRightAdjoint_hOverPullback_sheafPushforwardContinuous
    {f : X ⟶ Y} {A : Type v} [Category A] :
    ((Over.pullback f).sheafPushforwardContinuous A
      (H.Big.site Y) (H.Big.site X)).IsRightAdjoint :=
  (Scheme.hPrecoverage.toGrothendieck.overMapPushforwardAdjunction A f).isRightAdjoint

/-- The comparison morphism of topoi `a_X : Sh((Sch/X)_h) ⟶ Sh(X_étale)` given by the
composite `π_X ∘ ε_X`. -/
noncomputable def a (X : Scheme.{u}) :
    MorphismOfTopoiIn X.smallEtaleTopology (H.Big.site X) :=
  MorphismOfTopoiIn.comp (siteMorphismOfTopoi X) (epsilon X)

/-- Inverse image along `a X` is the composite `π_X⁻¹ ⋙ ε_X⁻¹`. -/
theorem a_inverseImage (X : Scheme.{u}) :
    (a X)⁻¹ = (siteMorphismOfTopoi X)⁻¹ ⋙ (epsilon X)⁻¹ := rfl

/-- Inverse image along `a X` is sheaf pullback of identity relocalization into the big h site. -/
noncomputable def aInverseImageIso (X : Scheme.{u}) :
    (a X)⁻¹ ≅
      (relocalizationFunctor (𝟙 X)).sheafPullback (Type (u + 1))
        X.smallEtaleTopology (H.Big.site X) :=
  let adjπ :=
    (relocalizationFunctor (𝟙 X)).sheafAdjunctionContinuous (Type (u + 1))
      X.smallEtaleTopology (X.overGrothendieckTopology @Etale)
  let adjε :=
    @Functor.sheafAdjunctionContinuous _ _ _ _ (𝟭 (Over X)) (Type (u + 1)) _
      (X.overGrothendieckTopology @Etale) (H.Big.site X)
      (identity_isMorphismOfSites X).toIsContinuous
      (@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        _ _ _ _ (𝟭 (Over X)) (Type (u + 1)) _
        (X.overGrothendieckTopology @Etale) (H.Big.site X)
        (identity_isMorphismOfSites X).toIsContinuous
        (fun _ => inferInstance) (H.Big.hasWeakSheafify X)).isRightAdjoint
  let adjH :=
    (relocalizationFunctor (𝟙 X)).sheafAdjunctionContinuous (Type (u + 1))
      X.smallEtaleTopology (H.Big.site X)
  Adjunction.leftAdjointCompIso adjπ adjε adjH
    (@Functor.sheafPushforwardContinuousComp' _ _ _ _ _ _ _ _ _
      (Functor.rightUnitor (relocalizationFunctor (𝟙 X))) (Type (u + 1))
      _ X.smallEtaleTopology (X.overGrothendieckTopology @Etale) (H.Big.site X)
      inferInstance (identity_isMorphismOfSites X).toIsContinuous inferInstance)

/-- The inverse image of the big h morphism of topoi is the sheaf pullback along
`Over.pullback f`. -/
noncomputable def bigHInverseImageIsoPullback (f : X ⟶ Y) :
    (H.Big.morphismOfTopoi f)⁻¹ ≅
      (Over.pullback f).sheafPullback (Type (u + 1)) (H.Big.site Y) (H.Big.site X) :=
  Adjunction.leftAdjointUniq
    (Scheme.hPrecoverage.toGrothendieck.overMapPushforwardAdjunction (Type (u + 1)) f)
    ((Over.pullback f).sheafAdjunctionContinuous (Type (u + 1))
      (H.Big.site Y) (H.Big.site X))

variable (f : X ⟶ Y)
variable [HasSheafify X.smallEtaleTopology (Type (u + 1))]
variable [HasSheafify Y.smallEtaleTopology (Type (u + 1))]

/-- Inverse-image square `a_Y⁻¹ ⋙ f_big,h⁻¹ ≅ f_small⁻¹ ⋙ a_X⁻¹` on sheaves of sets. -/
noncomputable def smallHInverseImageSquare :
    (a Y)⁻¹ ⋙ (H.Big.morphismOfTopoi f)⁻¹ ≅
      (smallMorphism f)⁻¹ ⋙ (a X)⁻¹ :=
  let adjY :=
    (relocalizationFunctor (𝟙 Y)).sheafAdjunctionContinuous (Type (u + 1))
      Y.smallEtaleTopology (H.Big.site Y)
  let adjX :=
    (relocalizationFunctor (𝟙 X)).sheafAdjunctionContinuous (Type (u + 1))
      X.smallEtaleTopology (H.Big.site X)
  let adjSmall :=
    (smallEtalePullback f).sheafAdjunctionContinuous (Type (u + 1))
      Y.smallEtaleTopology X.smallEtaleTopology
  let adjHPull :=
    (Over.pullback f).sheafAdjunctionContinuous (Type (u + 1))
      (H.Big.site Y) (H.Big.site X)
  Functor.isoWhiskerLeft ((a Y)⁻¹) (bigHInverseImageIsoPullback f) ≪≫
    Functor.isoWhiskerRight (aInverseImageIso Y)
      ((Over.pullback f).sheafPullback (Type (u + 1)) (H.Big.site Y) (H.Big.site X)) ≪≫
    Adjunction.leftAdjointCompIso adjY adjHPull (adjSmall.comp adjX)
      (Functor.sheafPushforwardContinuousComp'
          (smallBigRelocalizationSiteIso f).symm (Type (u + 1))
          Y.smallEtaleTopology (H.Big.site Y) (H.Big.site X) ≪≫
        (Functor.sheafPushforwardContinuousComp'
          (Iso.refl (smallEtalePullback f ⋙ relocalizationFunctor (𝟙 X)))
          (Type (u + 1)) Y.smallEtaleTopology X.smallEtaleTopology
          (H.Big.site X)).symm) ≪≫
    Functor.isoWhiskerLeft ((smallMorphism f)⁻¹) (aInverseImageIso X).symm

/-- Canonical Type-valued mate `a_Y⁻¹ ∘ f_small,* ⟶ f_big,h,* ∘ a_X⁻¹`. -/
noncomputable def smallHPushforwardHom :
    (smallMorphism f).pushforward ⋙ (a Y)⁻¹ ⟶
      (a X)⁻¹ ⋙ (H.Big.morphismOfTopoi f).pushforward :=
  DerivedBaseChange.map
    (smallMorphism f).adjunction
    (H.Big.morphismOfTopoi f).adjunction
    (smallHInverseImageSquare f)

/-- For a proper scheme morphism, the canonical comparison from small étale direct image
followed by inverse image to the big h topos to big h direct image after inverse image is
an isomorphism on sheaves of sets. -/
@[stacks 0EWA, instance]
theorem proper_smallHPushforward_isIso [IsProper f] :
    IsIso (smallHPushforwardHom f) := sorry

end AlgebraicGeometry.Scheme.HComparison

end

end
