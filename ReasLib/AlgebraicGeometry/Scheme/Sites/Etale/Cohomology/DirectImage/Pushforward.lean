module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.DirectImage.NormalizedInverseSystem

/-!
# Abelian pushforward systems of étale sheaves on inverse limits

This module packages the small-étale pushforwards `f_{i*} F` of an abelian sheaf
on a limit scheme as an `AbelianSheafSystem`, together with the counit comparison
`colim_i f_i⁻¹ f_{i*} F ⟶ F` and the specialized higher-direct-image comparison
`colim_i h_i⁻¹ R^p g_{i*}(f_{i*} F) ⟶ R^p g_* F`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (DX DS : OrderDual I ⥤ Scheme.{u})
variable [∀ i : I, HasSheafify (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasWeakSheafify (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I,
    HasInjectiveResolutions
      (Sheaf (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ i : I, HasSheafify (DS.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasWeakSheafify (DS.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ {T U : Scheme.{u}} (f : U ⟶ T)
    (G : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}),
    (smallEtalePullback f).op.HasLeftKanExtension G]
variable [∀ {T U : Scheme.{u}} (f : U ⟶ T),
    ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      T.smallEtaleTopology U.smallEtaleTopology).IsRightAdjoint]
variable (g : ∀ i : I, DX.obj (OrderDual.toDual i) ⟶ DS.obj (OrderDual.toDual i))
variable (hg : ∀ {i j : I} (hij : i ≤ j),
    OrderDualInverseSystem.transitionMap DX hij ≫ g i =
      g j ≫ OrderDualInverseSystem.transitionMap DS hij)
variable (cX : Cone DX) (cS : Cone DS)
variable (gX : cX.pt ⟶ cS.pt)
variable (hgX : ∀ i : I,
    cX.π.app (OrderDual.toDual i) ≫ g i = gX ≫ cS.π.app (OrderDual.toDual i))
variable [HasSheafify cS.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify cS.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify cX.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify cX.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasInjectiveResolutions (Sheaf cX.pt.smallEtaleTopology AddCommGrpCat.{u})]
variable (F : Sheaf cX.pt.smallEtaleTopology AddCommGrpCat.{u}) (p : ℕ)

/-- Direct image of an abelian small-étale sheaf along a morphism of schemes. -/
abbrev abelianPushforwardAlong {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
  ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      Y.smallEtaleTopology X.smallEtaleTopology).obj G

/-- Direct image of `F` along the cone projection `f_i : X ⟶ X_i`. -/
abbrev abelianStagePushforward (i : I) :
    Sheaf (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u} :=
  abelianPushforwardAlong (cX.π.app (OrderDual.toDual i)) F

/-- Direct image along a composite is the composite of the direct images. -/
def abelianPushforwardCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasWeakSheafify Z.smallEtaleTopology AddCommGrpCat.{u}] :
    (smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
        Y.smallEtaleTopology X.smallEtaleTopology ⋙
      (smallEtalePullback g).sheafPushforwardContinuous AddCommGrpCat.{u}
        Z.smallEtaleTopology Y.smallEtaleTopology ≅
      (smallEtalePullback (f ≫ g)).sheafPushforwardContinuous AddCommGrpCat.{u}
        Z.smallEtaleTopology X.smallEtaleTopology :=
  let siteIso :
      smallEtalePullback g ⋙ smallEtalePullback f ≅ smallEtalePullback (f ≫ g) :=
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g).symm
  @Functor.sheafPushforwardContinuousComp'
    Z.Etale inferInstance
    Y.Etale inferInstance
    X.Etale inferInstance
    (smallEtalePullback g) (smallEtalePullback f) (smallEtalePullback (f ≫ g))
    siteIso AddCommGrpCat.{u} inferInstance
    Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology
    (smallEtalePullback_isContinuous g)
    (smallEtalePullback_isContinuous f)
    (smallEtalePullback_isContinuous (f ≫ g))

/-- The adjunction mate `φ_{ji} : f_{ji}^{-1} f_{i*} F ⟶ f_{j*} F`. -/
def abelianStageTransition {i j : I} (hij : i ≤ j) :
    (transitionPullback DX hij).obj (abelianStagePushforward DX cX F i) ⟶
      abelianStagePushforward DX cX F j :=
  (((smallEtalePullback (OrderDualInverseSystem.transitionMap DX hij)).sheafAdjunctionContinuous
        AddCommGrpCat.{u}
        (DX.obj (OrderDual.toDual i)).smallEtaleTopology
        (DX.obj (OrderDual.toDual j)).smallEtaleTopology).homEquiv
      (abelianStagePushforward DX cX F i)
      (abelianStagePushforward DX cX F j)).symm
    (eqToHom
        (congrArg (fun t => abelianPushforwardAlong t F)
          (cX.w (homOfLE (OrderDual.toDual_le_toDual.mpr hij))).symm) ≫
      (abelianPushforwardCompIso (cX.π.app (OrderDual.toDual j))
          (OrderDualInverseSystem.transitionMap DX hij)).inv.app F)

/-- The inverse system of abelian small-étale pushforwards of `F` along the limit projections. -/
def abelianPushforwardSystem : AbelianSheafSystem DX :=
  AbelianSheafSystem.of (abelianStagePushforward DX cX F)
    (fun {i j} hij => abelianStageTransition DX cX F hij) (fun _ _ => sorry)

/-- The stage sheaf of `abelianPushforwardSystem` is the projection pushforward. -/
theorem abelianPushforwardSystem_obj (i : I) :
    (abelianPushforwardSystem DX cX F).obj i = abelianStagePushforward DX cX F i :=
  sorry

/-- The transition of `abelianPushforwardSystem` is the adjunction mate `φ`. -/
theorem abelianPushforwardSystem_transition {i j : I} (hij : i ≤ j) :
    (abelianPushforwardSystem DX cX F).transition hij =
      abelianStageTransition DX cX F hij :=
  sorry

variable [HasColimit (inverseImageDiagram DX cX (abelianPushforwardSystem DX cX F))]

/-- The cocone of stage counits with vertex `F`. -/
def abelianCounitCocone :
    Cocone (inverseImageDiagram DX cX (abelianPushforwardSystem DX cX F)) where
  pt := F
  ι :=
    { app := fun i =>
        (coneLegSheafAdjunction DX cX i).counit.app F
      naturality := fun _ _ _ => sorry }

/-- The comparison `colim_i f_i⁻¹ f_{i*} F ⟶ F` induced by the stage counits. -/
def counitComparison :
    colimitInverseImage DX cX (abelianPushforwardSystem DX cX F) ⟶ F :=
  colimit.desc (inverseImageDiagram DX cX (abelianPushforwardSystem DX cX F))
    (abelianCounitCocone DX cX F)

/-- The comparison restricts to the stage counit on each summand. -/
theorem counitComparison_ι (i : I) :
    colimitInverseImage_ι DX cX (abelianPushforwardSystem DX cX F) i ≫
        counitComparison DX cX F =
      (coneLegSheafAdjunction DX cX i).counit.app F :=
  sorry

/-- If the inverse system is a directed limit with affine transition morphisms, the
counit comparison is an isomorphism. -/
theorem counitComparison_isIso
    [∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap DX hij)]
    (hcX : IsLimit cX) :
    IsIso (counitComparison DX cX F) :=
  sorry

variable [HasColimit
  (higherDirectImage_pullbackDiagram DX DS g hg cS
    (abelianPushforwardSystem DX cX F) p)]

/-- The specialized comparison
`colim_i h_i⁻¹ R^p g_{i*}(f_{i*} F) ⟶ R^p g_* F`. -/
def higherDirectImage_stagePushforwardComparison :
    colimit (higherDirectImage_pullbackDiagram DX DS g hg cS
      (abelianPushforwardSystem DX cX F) p) ⟶
      schemeHigherDirectImage gX F p :=
  higherDirectImage_pullbackComparison DX DS g hg cX cS gX hgX
      (abelianPushforwardSystem DX cX F) p ≫
    schemeHigherDirectImageMap gX (counitComparison DX cX F) p

/-- The specialized comparison restricts to the normalized stage map composed with
`R^p g_*` of the counit. -/
theorem higherDirectImage_stagePushforwardComparison_ι (i : I) :
    colimit.ι (higherDirectImage_pullbackDiagram DX DS g hg cS
      (abelianPushforwardSystem DX cX F) p) i ≫
        higherDirectImage_stagePushforwardComparison DX DS g hg cX cS gX hgX F p =
      higherDirectImage_pullbackStageMap DX DS g cX cS gX hgX
          (abelianPushforwardSystem DX cX F) p i ≫
        schemeHigherDirectImageMap gX (counitComparison DX cX F) p :=
  sorry

/-- Higher direct image along the limit is the colimit of the pulled-back stage
higher direct images applied to the projected pushforwards. -/
theorem higherDirectImage_eq_colimit_stagePushforward
    [∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap DX hij)]
    [∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap DS hij)]
    [∀ i : I, QuasiCompact (g i)]
    [∀ i : I, QuasiSeparated (g i)]
    (hcX : IsLimit cX) (hcS : IsLimit cS) :
    IsIso (higherDirectImage_stagePushforwardComparison DX DS g hg cX cS gX hgX F p) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
