module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Covering
public import ReasLib.CategoryTheory.Sites.Topos.Retraction
public import ReasLib.CategoryTheory.Sites.Derived.SectionsComparison
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Change of universe for chosen small pro-étale sites

A scheme-compatible inclusion of chosen presentations induces a retraction of
small pro-étale topoi and canonical comparisons of abelian sheaf cohomology.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Functor
open scoped MorphismOfTopoiIn

noncomputable section

universe u v w

namespace AlgebraicGeometry.ChosenBigProetaleSite

variable {X Y : ChosenBigProetaleSite.{u, v}}

/-- Carrier postcomposition along a scheme-compatible functor preserves the
weakly étale object property of a chosen small pro-étale site. -/
theorem smallObjects_map_post (S : X.carrier) (ι : X.carrier ⥤ Y.carrier)
    (e : ι ⋙ Y.toScheme ≅ X.toScheme) (U : smallSite X S) :
    smallObjects Y (ι.obj S) ((smallInclusion X S ⋙ Over.post ι).obj U) := sorry

/-- The inclusion of nested chosen small pro-étale sites induced by a
scheme-compatible carrier functor. On objects it sends `U / S` in the smaller
presentation to the same structural morphism viewed in the larger
presentation. -/
def smallNestedInclusion (S : X.carrier) (ι : X.carrier ⥤ Y.carrier)
    (e : ι ⋙ Y.toScheme ≅ X.toScheme) :
    smallSite X S ⥤ smallSite Y (ι.obj S) :=
  (smallObjects Y (ι.obj S)).lift (smallInclusion X S ⋙ Over.post ι)
    (smallObjects_map_post S ι e)

/-- The nested small inclusion sits over carrier postcomposition via the
small-to-big inclusion of the larger presentation. -/
theorem smallNestedInclusion_obj (S : X.carrier) (ι : X.carrier ⥤ Y.carrier)
    (e : ι ⋙ Y.toScheme ≅ X.toScheme) (U : smallSite X S) :
    (smallInclusion Y (ι.obj S)).obj ((smallNestedInclusion S ι e).obj U) =
      (Over.post ι).obj U.obj := sorry

/-- The nested small inclusion triangle is the identity after including into
the larger chosen big slice. -/
def smallNestedInclusion_comp_smallInclusion (S : X.carrier)
    (ι : X.carrier ⥤ Y.carrier) (e : ι ⋙ Y.toScheme ≅ X.toScheme) :
    smallNestedInclusion S ι e ⋙ smallInclusion Y (ι.obj S) ≅
      smallInclusion X S ⋙ Over.post ι :=
  (smallObjects Y (ι.obj S)).liftCompιIso (smallInclusion X S ⋙ Over.post ι)
    (smallObjects_map_post S ι e)

/-- The nested small-inclusion triangle isomorphism is the identity on
objects of the larger chosen big slice. -/
theorem smallNestedInclusion_comp_smallInclusion_hom_app (S : X.carrier)
    (ι : X.carrier ⥤ Y.carrier) (e : ι ⋙ Y.toScheme ≅ X.toScheme)
    (U : smallSite X S) :
    (smallNestedInclusion_comp_smallInclusion S ι e).hom.app U =
      𝟙 ((smallNestedInclusion S ι e ⋙ smallInclusion Y (ι.obj S)).obj U) := sorry

/-- The nested small inclusion sends `S / S` to the identity object of the
larger small site. -/
def smallNestedInclusion_obj_smallTerminalObject_iso (S : X.carrier)
    (ι : X.carrier ⥤ Y.carrier) (e : ι ⋙ Y.toScheme ≅ X.toScheme) :
    (smallNestedInclusion S ι e).obj (smallTerminalObject X S) ≅
      smallTerminalObject Y (ι.obj S) :=
  (smallObjects Y (ι.obj S)).isoMk (eqToIso (congrArg Over.mk (ι.map_id S)))

/-- The identity-object identification for the nested small inclusion is the
identity on the underlying source scheme of the larger presentation. -/
theorem smallNestedInclusion_obj_smallTerminalObject_iso_hom_left (S : X.carrier)
    (ι : X.carrier ⥤ Y.carrier) (e : ι ⋙ Y.toScheme ≅ X.toScheme) :
    ((smallInclusion Y (ι.obj S)).map
        (smallNestedInclusion_obj_smallTerminalObject_iso S ι e).hom).left =
      𝟙 (ι.obj S) := sorry

/-- The nested small inclusion sends the final object `S / S` of the smaller
site to a final object of the larger small site. -/
def smallNestedInclusion_obj_smallTerminalObject (S : X.carrier)
    (ι : X.carrier ⥤ Y.carrier) (e : ι ⋙ Y.toScheme ≅ X.toScheme) :
    IsTerminal ((smallNestedInclusion S ι e).obj (smallTerminalObject X S)) :=
  (smallTerminalObjectIsTerminal Y (ι.obj S)).ofIso
    (smallNestedInclusion_obj_smallTerminalObject_iso S ι e).symm

/-- The scheme-compatible nested small inclusion is full. -/
theorem smallNestedInclusion_full (S : X.carrier) (ι : X.carrier ⥤ Y.carrier)
    (e : ι ⋙ Y.toScheme ≅ X.toScheme) :
    (smallNestedInclusion S ι e).Full := sorry

/-- The scheme-compatible nested small inclusion is faithful. -/
theorem smallNestedInclusion_faithful (S : X.carrier) (ι : X.carrier ⥤ Y.carrier)
    (e : ι ⋙ Y.toScheme ≅ X.toScheme) :
    (smallNestedInclusion S ι e).Faithful := sorry

/-- The nested small inclusion is continuous for the chosen small pro-étale
topologies inherited from the scheme covering specifications. -/
theorem smallNestedInclusion_isContinuous (S : X.carrier)
    (ι : X.carrier ⥤ Y.carrier) (e : ι ⋙ Y.toScheme ≅ X.toScheme)
    :
    (smallNestedInclusion S ι e).IsContinuous (smallTopology X S)
      (smallTopology Y (ι.obj S)) := sorry

/-- The nested small inclusion is cocontinuous for the chosen small pro-étale
topologies. -/
theorem smallNestedInclusion_isCocontinuous (S : X.carrier)
    (ι : X.carrier ⥤ Y.carrier) (e : ι ⋙ Y.toScheme ≅ X.toScheme) :
    (smallNestedInclusion S ι e).IsCocontinuous (smallTopology X S)
      (smallTopology Y (ι.obj S)) := sorry

/-- The nested small inclusion preserves fibre products. -/
theorem smallNestedInclusion_preservesPullbacks (S : X.carrier)
    (ι : X.carrier ⥤ Y.carrier) (e : ι ⋙ Y.toScheme ≅ X.toScheme) :
    PreservesLimitsOfShape WalkingCospan (smallNestedInclusion S ι e) := sorry

/-- Continuous pullback of set-valued sheaves along the nested inclusion preserves finite limits. -/
theorem smallNestedInclusion_sheafPullback_preservesFiniteLimits (S : X.carrier) (ι : X.carrier ⥤ Y.carrier)
    (e : ι ⋙ Y.toScheme ≅ X.toScheme)
    [HasWeakSheafify (smallTopology Y (ι.obj S)) (Type w)]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ (Type w),
      (smallNestedInclusion S ι e).op.HasLeftKanExtension P]
    : PreservesFiniteLimits (@Functor.sheafPullback _ _ _ _ (smallNestedInclusion S ι e) (Type w) _
        (smallTopology X S) (smallTopology Y (ι.obj S)) (smallNestedInclusion_isContinuous S ι e)
        (@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _ (smallNestedInclusion S ι e)
        (Type w) _ (smallTopology X S) (smallTopology Y (ι.obj S)) (smallNestedInclusion_isContinuous S ι e)
        inferInstance inferInstance).isRightAdjoint) :=
  sorry

/-- The continuous morphism from the larger chosen small pro-étale topos to the smaller one. -/
def smallNestedInclusion_continuousMorphism (S : X.carrier) (ι : X.carrier ⥤ Y.carrier)
    (e : ι ⋙ Y.toScheme ≅ X.toScheme)
    [HasWeakSheafify (smallTopology Y (ι.obj S)) (Type w)]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ (Type w),
      (smallNestedInclusion S ι e).op.HasLeftKanExtension P]
    : MorphismOfTopoiIn.{max u v, max u v, u, u, w} (smallTopology X S) (smallTopology Y (ι.obj S)) :=
  (@Functor.morphismOfTopoiInOfContinuous _ _ _ _ (smallNestedInclusion S ι e) (smallTopology X S)
      (smallTopology Y (ι.obj S)) (smallNestedInclusion_isContinuous S ι e) inferInstance inferInstance
      (smallNestedInclusion_sheafPullback_preservesFiniteLimits S ι e))

/-- The cocontinuous morphism from the smaller chosen small pro-étale topos to the larger one. -/
def smallNestedInclusion_cocontinuousMorphism (S : X.carrier) (ι : X.carrier ⥤ Y.carrier)
    (e : ι ⋙ Y.toScheme ≅ X.toScheme)
    [HasSheafify (smallTopology X S) (Type w)]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ (Type w),
      (smallNestedInclusion S ι e).op.HasPointwiseRightKanExtension P]
    : MorphismOfTopoiIn.{max u v, max u v, u, u, w} (smallTopology Y (ι.obj S)) (smallTopology X S) :=
  (@Functor.morphismOfTopoiInOfCocontinuous _ _ _ _ (smallNestedInclusion S ι e) (smallTopology X S)
      (smallTopology Y (ι.obj S)) (smallNestedInclusion_isCocontinuous S ι e) inferInstance inferInstance)

/-- The continuous and cocontinuous topos morphisms form a retraction on inverse images. -/
def smallNestedInclusion_comp_inverseImageIso (S : X.carrier) (ι : X.carrier ⥤ Y.carrier)
    (e : ι ⋙ Y.toScheme ≅ X.toScheme)
    [HasSheafify (smallTopology X S) (Type w)]
    [HasWeakSheafify (smallTopology Y (ι.obj S)) (Type w)]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ (Type w),
      (smallNestedInclusion S ι e).op.HasLeftKanExtension P]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ (Type w),
      (smallNestedInclusion S ι e).op.HasPointwiseLeftKanExtension P]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ (Type w),
      (smallNestedInclusion S ι e).op.HasPointwiseRightKanExtension P]
    : (MorphismOfTopoiIn.comp (smallNestedInclusion_continuousMorphism.{u, v, w} S ι e)
      (smallNestedInclusion_cocontinuousMorphism.{u, v, w} S ι e)).inverseImage ≅
      (MorphismOfTopoiIn.id (smallTopology X S)).inverseImage :=
  (@Retraction.compInverseImageIso _ _ _ _ (smallTopology X S) (smallTopology Y (ι.obj S))
      (smallNestedInclusion S ι e) (smallNestedInclusion_full S ι e) (smallNestedInclusion_faithful S ι e)
      (smallNestedInclusion_isContinuous S ι e) (smallNestedInclusion_isCocontinuous S ι e) inferInstance
      inferInstance inferInstance (smallNestedInclusion_sheafPullback_preservesFiniteLimits S ι e)
      inferInstance inferInstance)

/-- The forward retraction map is the canonical continuous-adjunction retraction map. -/
theorem smallNestedInclusion_comp_inverseImageIso_hom (S : X.carrier) (ι : X.carrier ⥤ Y.carrier)
    (e : ι ⋙ Y.toScheme ≅ X.toScheme)
    [HasSheafify (smallTopology X S) (Type w)]
    [HasWeakSheafify (smallTopology Y (ι.obj S)) (Type w)]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ (Type w),
      (smallNestedInclusion S ι e).op.HasLeftKanExtension P]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ (Type w),
      (smallNestedInclusion S ι e).op.HasPointwiseLeftKanExtension P]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ (Type w),
      (smallNestedInclusion S ι e).op.HasPointwiseRightKanExtension P]
    : (smallNestedInclusion_comp_inverseImageIso S ι e).hom = (@Retraction.compInverseImageIso _ _ _ _
        (smallTopology X S) (smallTopology Y (ι.obj S)) (smallNestedInclusion S ι e)
        (smallNestedInclusion_full S ι e) (smallNestedInclusion_faithful S ι e)
        (smallNestedInclusion_isContinuous S ι e) (smallNestedInclusion_isCocontinuous S ι e) inferInstance
        inferInstance inferInstance (smallNestedInclusion_sheafPullback_preservesFiniteLimits S ι e)
        inferInstance inferInstance).hom :=
  rfl

/-- Cocontinuous inverse image is canonically isomorphic to continuous direct image. -/
def smallNestedInclusion_pushforward_iso_inverseImage (S : X.carrier) (ι : X.carrier ⥤ Y.carrier)
    (e : ι ⋙ Y.toScheme ≅ X.toScheme)
    [HasSheafify (smallTopology X S) (Type w)]
    [HasWeakSheafify (smallTopology Y (ι.obj S)) (Type w)]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ (Type w),
      (smallNestedInclusion S ι e).op.HasLeftKanExtension P]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ (Type w),
      (smallNestedInclusion S ι e).op.HasPointwiseRightKanExtension P]
    : (smallNestedInclusion_cocontinuousMorphism.{u, v, w} S ι e)⁻¹ ≅
      (smallNestedInclusion_continuousMorphism.{u, v, w} S ι e)_* :=
  (@CocontinuousPullback.comparisonIso.{w} _ _ _ _ (smallNestedInclusion S ι e) (smallTopology X S)
      (smallTopology Y (ι.obj S)) inferInstance inferInstance (smallNestedInclusion_isContinuous S ι e)
      (smallNestedInclusion_isCocontinuous S ι e) inferInstance)

/-- The forward inverse-image comparison is the canonical sheafification comparison. -/
theorem smallNestedInclusion_pushforward_iso_inverseImage_hom (S : X.carrier) (ι : X.carrier ⥤ Y.carrier)
    (e : ι ⋙ Y.toScheme ≅ X.toScheme)
    [HasSheafify (smallTopology X S) (Type w)]
    [HasWeakSheafify (smallTopology Y (ι.obj S)) (Type w)]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ (Type w),
      (smallNestedInclusion S ι e).op.HasLeftKanExtension P]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ (Type w),
      (smallNestedInclusion S ι e).op.HasPointwiseRightKanExtension P]
    : (smallNestedInclusion_pushforward_iso_inverseImage S ι e).hom =
      (@CocontinuousPullback.comparison.{w} _ _ _ _ (smallNestedInclusion S ι e) (smallTopology X S)
          (smallTopology Y (ι.obj S)) inferInstance inferInstance (smallNestedInclusion_isContinuous S ι e)
          (smallNestedInclusion_isCocontinuous S ι e) inferInstance) :=
  rfl

/-- Restriction of abelian sheaves from the larger chosen small site to the smaller one. -/
def smallNestedInclusion_abelianRestriction (S : X.carrier) (ι : X.carrier ⥤ Y.carrier)
    (e : ι ⋙ Y.toScheme ≅ X.toScheme)
    : Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w} ⥤ Sheaf (smallTopology X S) AddCommGrpCat.{w} :=
  (@Functor.sheafPushforwardContinuous _ _ _ _ (smallNestedInclusion S ι e) AddCommGrpCat.{w} _
      (smallTopology X S) (smallTopology Y (ι.obj S)) (smallNestedInclusion_isContinuous S ι e))

/-- Cocontinuous direct image of abelian sheaves to the larger chosen small site. -/
def smallNestedInclusion_abelianPushforward (S : X.carrier) (ι : X.carrier ⥤ Y.carrier)
    (e : ι ⋙ Y.toScheme ≅ X.toScheme)
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasPointwiseRightKanExtension P]
    : Sheaf (smallTopology X S) AddCommGrpCat.{w} ⥤ Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w} :=
  (@Functor.sheafPushforwardCocontinuous _ _ _ _ (smallNestedInclusion S ι e) AddCommGrpCat.{w} _
      (smallTopology X S) (smallTopology Y (ι.obj S)) (smallNestedInclusion_isCocontinuous S ι e)
      inferInstance)

/-- Continuous inverse image of abelian sheaves to the larger chosen small site. -/
def smallNestedInclusion_abelianPullback (S : X.carrier) (ι : X.carrier ⥤ Y.carrier)
    (e : ι ⋙ Y.toScheme ≅ X.toScheme)
    [HasWeakSheafify (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasLeftKanExtension P]
    : Sheaf (smallTopology X S) AddCommGrpCat.{w} ⥤ Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w} :=
  (@Functor.sheafPullback _ _ _ _ (smallNestedInclusion S ι e) AddCommGrpCat.{w} _ (smallTopology X S)
      (smallTopology Y (ι.obj S)) (smallNestedInclusion_isContinuous S ι e)
      (@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _ (smallNestedInclusion S ι e)
      AddCommGrpCat.{w} _ (smallTopology X S) (smallTopology Y (ι.obj S)) (smallNestedInclusion_isContinuous
      S ι e) inferInstance inferInstance).isRightAdjoint)

/-- Continuous inverse image of abelian sheaves along the nested inclusion preserves finite limits. -/
theorem smallNestedInclusion_abelianPullback_preservesFiniteLimits (S : X.carrier) (ι : X.carrier ⥤
    Y.carrier)
    (e : ι ⋙ Y.toScheme ≅ X.toScheme)
    [HasSheafify (smallTopology X S) AddCommGrpCat.{w}]
    [HasSheafify (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasLeftKanExtension P]
    : PreservesFiniteLimits (smallNestedInclusion_abelianPullback.{u, v, w} S ι e) :=
  sorry

/-- Restriction along the nested inclusion preserves injective abelian sheaves by its left-exact left
    adjoint. -/
theorem smallNestedInclusion_abelianRestriction_preservesInjectiveObjects (S : X.carrier) (ι : X.carrier ⥤
    Y.carrier)
    (e : ι ⋙ Y.toScheme ≅ X.toScheme)
    [HasSheafify (smallTopology X S) AddCommGrpCat.{w}]
    [HasSheafify (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasLeftKanExtension P]
    : (smallNestedInclusion_abelianRestriction.{u, v, w} S ι e).PreservesInjectiveObjects :=
  (@Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms _ _ _ _
    (smallNestedInclusion_abelianPullback.{u, v, w} S ι e) (smallNestedInclusion_abelianRestriction.{u, v,
        w} S ι e) (@Functor.sheafAdjunctionContinuous _ _ _ _ (smallNestedInclusion S ι e) AddCommGrpCat.{w}
        _ (smallTopology X S) (smallTopology Y (ι.obj S)) (smallNestedInclusion_isContinuous S ι e)
        (@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _ (smallNestedInclusion S ι e)
        AddCommGrpCat.{w} _ (smallTopology X S) (smallTopology Y (ι.obj S))
        (smallNestedInclusion_isContinuous S ι e) inferInstance inferInstance).isRightAdjoint)
        (@preservesMonomorphisms_of_preservesLimitsOfShape _ _ _ _ (smallNestedInclusion_abelianPullback.{u,
        v, w} S ι e)
      (@PreservesFiniteLimits.preservesFiniteLimits _ _ _ _ (smallNestedInclusion_abelianPullback.{u, v, w}
          S ι e)
        (smallNestedInclusion_abelianPullback_preservesFiniteLimits S ι e) WalkingCospan inferInstance
            inferInstance)))

/-- Derived global sections of a restricted abelian sheaf agree with those on the larger site. -/
def smallNestedInclusion_cohomology_restrict (S : X.carrier) (ι : X.carrier ⥤ Y.carrier)
    (e : ι ⋙ Y.toScheme ≅ X.toScheme)
    [HasSheafify (smallTopology X S) AddCommGrpCat.{w}]
    [HasSheafify (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology X S) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [IsGrothendieckAbelian (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasLeftKanExtension P]
    (p : ℕ) (F' : Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})
    : ((Sheaf.Γ (smallTopology X S) AddCommGrpCat.{w}).rightDerived p).obj
        ((smallNestedInclusion_abelianRestriction.{u, v, w} S ι e).obj F') ≅ ((Sheaf.Γ (smallTopology Y
        (ι.obj S)) AddCommGrpCat.{w}).rightDerived p).obj F' :=
  (@RightDerived.precompObjIso _ _ _ _ _ _ _ _ _ (smallNestedInclusion_abelianRestriction.{u, v, w} S ι e)
      (Sheaf.Γ (smallTopology X S) AddCommGrpCat.{w})
      (@Functor.sheafPushforwardContinuous_additive _ _ _ _ (smallNestedInclusion S ι e) (smallTopology X S)
          (smallTopology Y (ι.obj S)) (smallNestedInclusion_isContinuous S ι e)) inferInstance
          (smallNestedInclusion_abelianRestriction_preservesInjectiveObjects S ι e)
      (inferInstance : (@siteAbelianInverseImageExact _ _ _ _ (smallTopology X S) (smallTopology Y (ι.obj
          S)) (smallNestedInclusion S ι e) (smallNestedInclusion_isContinuous S ι e)
          (smallNestedInclusion_isCocontinuous S ι e) inferInstance inferInstance).obj.PreservesHomology)
          inferInstance inferInstance p F').symm ≪≫
    ((@SiteAbelianSectionsDerived.derivedGlobalSectionsIso _ _ _ _ (smallTopology X S) (smallTopology Y
        (ι.obj S)) (smallNestedInclusion S ι e)
      (smallNestedInclusion_isContinuous S ι e) (smallNestedInclusion_isCocontinuous S ι e) inferInstance
          inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance p (smallTerminalObject X S)
      (smallTerminalObjectIsTerminal X S)
      (smallNestedInclusion_obj_smallTerminalObject S ι e)).app F')

/-- The restriction comparison is derived precomposition followed by the terminal global-sections
    comparison. -/
theorem smallNestedInclusion_cohomology_restrict_eq (S : X.carrier) (ι : X.carrier ⥤ Y.carrier)
    (e : ι ⋙ Y.toScheme ≅ X.toScheme)
    [HasSheafify (smallTopology X S) AddCommGrpCat.{w}]
    [HasSheafify (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology X S) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [IsGrothendieckAbelian (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasLeftKanExtension P]
    (p : ℕ) (F' : Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})
    : smallNestedInclusion_cohomology_restrict S ι e p F' =
      (@RightDerived.precompObjIso _ _ _ _ _ _ _ _ _ (smallNestedInclusion_abelianRestriction.{u, v, w} S ι
          e) (Sheaf.Γ (smallTopology X S) AddCommGrpCat.{w})
      (@Functor.sheafPushforwardContinuous_additive _ _ _ _ (smallNestedInclusion S ι e) (smallTopology X S)
          (smallTopology Y (ι.obj S)) (smallNestedInclusion_isContinuous S ι e)) inferInstance
          (smallNestedInclusion_abelianRestriction_preservesInjectiveObjects S ι e)
      (inferInstance : (@siteAbelianInverseImageExact _ _ _ _ (smallTopology X S) (smallTopology Y (ι.obj
          S)) (smallNestedInclusion S ι e) (smallNestedInclusion_isContinuous S ι e)
          (smallNestedInclusion_isCocontinuous S ι e) inferInstance inferInstance).obj.PreservesHomology)
          inferInstance inferInstance p F').symm ≪≫
    ((@SiteAbelianSectionsDerived.derivedGlobalSectionsIso _ _ _ _ (smallTopology X S) (smallTopology Y
        (ι.obj S)) (smallNestedInclusion S ι e)
      (smallNestedInclusion_isContinuous S ι e) (smallNestedInclusion_isCocontinuous S ι e) inferInstance
          inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance p (smallTerminalObject X S)
      (smallTerminalObjectIsTerminal X S)
      (smallNestedInclusion_obj_smallTerminalObject S ι e)).app F') :=
  rfl

/-- Derived global sections agree with those of the canonical pushforward of an abelian sheaf. -/
def smallNestedInclusion_cohomology_pushforward (S : X.carrier) (ι : X.carrier ⥤ Y.carrier)
    (e : ι ⋙ Y.toScheme ≅ X.toScheme)
    [HasSheafify (smallTopology X S) AddCommGrpCat.{w}]
    [HasSheafify (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology X S) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [IsGrothendieckAbelian (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasLeftKanExtension P]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasPointwiseRightKanExtension P]
    (p : ℕ) (F : Sheaf (smallTopology X S) AddCommGrpCat.{w})
    : ((Sheaf.Γ (smallTopology X S) AddCommGrpCat.{w}).rightDerived p).obj F ≅ ((Sheaf.Γ (smallTopology Y
        (ι.obj S)) AddCommGrpCat.{w}).rightDerived p).obj ((smallNestedInclusion_abelianPushforward.{u, v,
        w} S ι e).obj F) :=
  ((Sheaf.Γ (smallTopology X S) AddCommGrpCat.{w}).rightDerived p).mapIso (@asIso _ _ _ _
      ((@Functor.sheafAdjunctionCocontinuous _ _ _ _ (smallNestedInclusion S ι e) AddCommGrpCat.{w} _
      (smallTopology X S) (smallTopology Y (ι.obj S)) (smallNestedInclusion_isCocontinuous S ι e)
      inferInstance (smallNestedInclusion_isContinuous S ι e)).counit.app F)
        (@Functor.FullyFaithful.sheafAdjunctionCocontinuous_counit_app_isIso
          _ _ _ _ (smallTopology X S) (smallTopology Y (ι.obj S)) (smallNestedInclusion S ι e)
              AddCommGrpCat.{w} _ (@Functor.FullyFaithful.ofFullyFaithful _ _ _ _ (smallNestedInclusion S ι
              e) (smallNestedInclusion_full S ι e) (smallNestedInclusion_faithful S ι e))
              (smallNestedInclusion_isContinuous S ι e) (smallNestedInclusion_isCocontinuous S ι e)
              inferInstance F)).symm ≪≫
    smallNestedInclusion_cohomology_restrict S ι e p ((smallNestedInclusion_abelianPushforward.{u, v, w} S ι
        e).obj F)

/-- The forward cohomology pushforward map is induced by the adjunction counit and the restriction
    comparison. -/
theorem smallNestedInclusion_cohomology_pushforward_hom (S : X.carrier) (ι : X.carrier ⥤ Y.carrier)
    (e : ι ⋙ Y.toScheme ≅ X.toScheme)
    [HasSheafify (smallTopology X S) AddCommGrpCat.{w}]
    [HasSheafify (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology X S) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [IsGrothendieckAbelian (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasLeftKanExtension P]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasPointwiseRightKanExtension P]
    (p : ℕ) (F : Sheaf (smallTopology X S) AddCommGrpCat.{w})
    : (smallNestedInclusion_cohomology_pushforward S ι e p F).hom =
      (((Sheaf.Γ (smallTopology X S) AddCommGrpCat.{w}).rightDerived p).mapIso (@asIso _ _ _ _
          ((@Functor.sheafAdjunctionCocontinuous _ _ _ _ (smallNestedInclusion S ι e) AddCommGrpCat.{w} _
          (smallTopology X S) (smallTopology Y (ι.obj S)) (smallNestedInclusion_isCocontinuous S ι e)
          inferInstance (smallNestedInclusion_isContinuous S ι e)).counit.app F)
        (@Functor.FullyFaithful.sheafAdjunctionCocontinuous_counit_app_isIso
          _ _ _ _ (smallTopology X S) (smallTopology Y (ι.obj S)) (smallNestedInclusion S ι e)
              AddCommGrpCat.{w} _ (@Functor.FullyFaithful.ofFullyFaithful _ _ _ _ (smallNestedInclusion S ι
              e) (smallNestedInclusion_full S ι e) (smallNestedInclusion_faithful S ι e))
              (smallNestedInclusion_isContinuous S ι e) (smallNestedInclusion_isCocontinuous S ι e)
              inferInstance F)).symm ≪≫
    smallNestedInclusion_cohomology_restrict S ι e p ((smallNestedInclusion_abelianPushforward.{u, v, w} S ι
        e).obj F)).hom :=
  rfl

/-- Derived global sections agree with those of the canonical pullback of an abelian sheaf. -/
def smallNestedInclusion_cohomology_pullback (S : X.carrier) (ι : X.carrier ⥤ Y.carrier)
    (e : ι ⋙ Y.toScheme ≅ X.toScheme)
    [HasSheafify (smallTopology X S) AddCommGrpCat.{w}]
    [HasSheafify (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology X S) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [IsGrothendieckAbelian (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasLeftKanExtension P]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasPointwiseLeftKanExtension P]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasPointwiseRightKanExtension P]
    (p : ℕ) (F : Sheaf (smallTopology X S) AddCommGrpCat.{w})
    : ((Sheaf.Γ (smallTopology X S) AddCommGrpCat.{w}).rightDerived p).obj F ≅ ((Sheaf.Γ (smallTopology Y
        (ι.obj S)) AddCommGrpCat.{w}).rightDerived p).obj ((smallNestedInclusion_abelianPullback.{u, v, w} S
        ι e).obj F) :=
  ((Sheaf.Γ (smallTopology X S) AddCommGrpCat.{w}).rightDerived p).mapIso (@asIso _ _ _ _
      ((@Functor.sheafAdjunctionContinuous _ _ _ _ (smallNestedInclusion S ι e) AddCommGrpCat.{w} _
      (smallTopology X S) (smallTopology Y (ι.obj S)) (smallNestedInclusion_isContinuous S ι e)
      (@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _ (smallNestedInclusion S ι e)
      AddCommGrpCat.{w} _ (smallTopology X S) (smallTopology Y (ι.obj S)) (smallNestedInclusion_isContinuous
      S ι e) inferInstance inferInstance).isRightAdjoint).unit.app F)
        (@Functor.FullyFaithful.sheafAdjunctionContinuous_unit_app_isIso
          _ _ _ _ (smallTopology X S) (smallTopology Y (ι.obj S)) (smallNestedInclusion S ι e)
              AddCommGrpCat.{w} _ (@Functor.FullyFaithful.ofFullyFaithful _ _ _ _ (smallNestedInclusion S ι
              e) (smallNestedInclusion_full S ι e) (smallNestedInclusion_faithful S ι e))
              (smallNestedInclusion_isContinuous S ι e) (smallNestedInclusion_isCocontinuous S ι e)
              inferInstance inferInstance inferInstance F inferInstance inferInstance)) ≪≫
    smallNestedInclusion_cohomology_restrict S ι e p ((smallNestedInclusion_abelianPullback.{u, v, w} S ι
        e).obj F)

/-- The forward cohomology pullback map is induced by the adjunction unit and the restriction comparison. -/
theorem smallNestedInclusion_cohomology_pullback_hom (S : X.carrier) (ι : X.carrier ⥤ Y.carrier)
    (e : ι ⋙ Y.toScheme ≅ X.toScheme)
    [HasSheafify (smallTopology X S) AddCommGrpCat.{w}]
    [HasSheafify (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology X S) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [IsGrothendieckAbelian (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasLeftKanExtension P]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasPointwiseLeftKanExtension P]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasPointwiseRightKanExtension P]
    (p : ℕ) (F : Sheaf (smallTopology X S) AddCommGrpCat.{w})
    : (smallNestedInclusion_cohomology_pullback S ι e p F).hom =
      (((Sheaf.Γ (smallTopology X S) AddCommGrpCat.{w}).rightDerived p).mapIso (@asIso _ _ _ _
          ((@Functor.sheafAdjunctionContinuous _ _ _ _ (smallNestedInclusion S ι e) AddCommGrpCat.{w} _
          (smallTopology X S) (smallTopology Y (ι.obj S)) (smallNestedInclusion_isContinuous S ι e)
          (@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _ (smallNestedInclusion S ι e)
          AddCommGrpCat.{w} _ (smallTopology X S) (smallTopology Y (ι.obj S))
          (smallNestedInclusion_isContinuous S ι e) inferInstance inferInstance).isRightAdjoint).unit.app F)
        (@Functor.FullyFaithful.sheafAdjunctionContinuous_unit_app_isIso
          _ _ _ _ (smallTopology X S) (smallTopology Y (ι.obj S)) (smallNestedInclusion S ι e)
              AddCommGrpCat.{w} _ (@Functor.FullyFaithful.ofFullyFaithful _ _ _ _ (smallNestedInclusion S ι
              e) (smallNestedInclusion_full S ι e) (smallNestedInclusion_faithful S ι e))
              (smallNestedInclusion_isContinuous S ι e) (smallNestedInclusion_isCocontinuous S ι e)
              inferInstance inferInstance inferInstance F inferInstance inferInstance)) ≪≫
    smallNestedInclusion_cohomology_restrict S ι e p ((smallNestedInclusion_abelianPullback.{u, v, w} S ι
        e).obj F)).hom :=
  rfl

end AlgebraicGeometry.ChosenBigProetaleSite
