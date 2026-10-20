/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Definition
public import Mathlib.CategoryTheory.Action.Continuous
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Pullback
public import ReasLib.CategoryTheory.Sites.Pullback.SliceComparison
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty CategoryTheory.Action.ModuleCat
open AlgebraicGeometry
universe u v w
namespace AlgebraicGeometry.Scheme
variable {Y X : Scheme.{u}} (f : Y ⟶ X)

/-- Constant sheaves pull back through the actual constant/global-section adjunctions. -/
noncomputable def constantSheafBaseChangeIso
    (D : Type v) [Category.{w} D]
    [HasWeakSheafify Y.smallEtaleTopology D]
    [HasWeakSheafify X.smallEtaleTopology D]
    [∀ P : X.Etaleᵒᵖ ⥤ D, (smallEtalePullback f).op.HasLeftKanExtension P]
    (A : D) :
    ((smallEtalePullback f).sheafPullback D X.smallEtaleTopology Y.smallEtaleTopology).obj
      ((constantSheaf X.smallEtaleTopology D).obj A) ≅
        (constantSheaf Y.smallEtaleTopology D).obj A := by
  let t : X.Etale := MorphismProperty.Over.mk _ (𝟙 X) inferInstance
  let ht : IsTerminal t := MorphismProperty.Over.mkIdTerminal (@Etale) X
  letI : PreservesFiniteLimits (smallEtalePullback f) :=
    inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.pullback @Etale ⊤ f))
  let ht' : IsTerminal ((smallEtalePullback f).obj t) :=
    ht.isTerminalObj (smallEtalePullback f)
  exact (((constantSheafAdj X.smallEtaleTopology D ht).comp
      (smallEtalePullback_sheafAdjunction f D)).leftAdjointUniq
        (constantSheafAdj Y.smallEtaleTopology D ht')).app A

/-- Base change on slice sites is continuous, with its native finite-limit preservation. -/
instance smallEtalePullback_overPost_isContinuous (V : X.Etale) :
    (Over.post (smallEtalePullback f) : Over V ⥤ _).IsContinuous
      (X.smallEtaleTopology.over V) (Y.smallEtaleTopology.over _) := sorry

/-- The actual pulled chart family preserves each supplied coefficient-model predicate. -/
theorem smallEtalePullback_isLocallyConstantWith
    (D : Type v) [Category.{w} D]
    [∀ Q : X.Etaleᵒᵖ ⥤ D, (smallEtalePullback f).op.HasLeftKanExtension Q]
    [HasLimitsOfSize.{u, u + 1} D] [HasColimitsOfSize.{u, u + 1} D]
    [HasWeakSheafify Y.smallEtaleTopology D]
    [HasWeakSheafify X.smallEtaleTopology D]
    [∀ V : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over V) D]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) D]
    (P : D → Prop) (G : Sheaf X.smallEtaleTopology D)
    (hG : Sheaf.IsLocallyConstantWith (J := X.smallEtaleTopology) P G) :
    Sheaf.IsLocallyConstantWith (J := Y.smallEtaleTopology) P
      (((smallEtalePullback f).sheafPullback D X.smallEtaleTopology Y.smallEtaleTopology).obj G) := by
  let F := smallEtalePullback f
  letI : PreservesFiniteLimits F :=
    inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.pullback @Etale ⊤ f))
  letI : ∀ Q : X.Etaleᵒᵖ ⥤ D, F.op.HasPointwiseLeftKanExtension Q := fun Q T ↦ by
    change HasColimit (CostructuredArrow.proj F.op T ⋙ Q)
    infer_instance
  letI : ∀ V : X.Etale, ∀ Q : (Over V)ᵒᵖ ⥤ D,
      (Over.post F).op.HasPointwiseLeftKanExtension Q := fun V Q T ↦ by
    change HasColimit (CostructuredArrow.proj (Over.post F).op T ⋙ Q)
    infer_instance
  letI : ∀ U : Y.Etale, ∀ Q : (Over U)ᵒᵖ ⥤ D,
      (Over.forget U).op.HasPointwiseRightKanExtension Q := fun U Q T ↦ by
    change HasLimit (StructuredArrow.proj T (Over.forget U).op ⋙ Q)
    infer_instance
  letI : ∀ U V : Y.Etale, ∀ g : U ⟶ V, ∀ Q : (Over U)ᵒᵖ ⥤ D,
      (Over.map g).op.HasPointwiseRightKanExtension Q := fun U V g Q T ↦ by
    change HasLimit (StructuredArrow.proj T (Over.map g).op ⋙ Q)
    infer_instance
  let t : X.Etale := MorphismProperty.Over.mk _ (𝟙 X) inferInstance
  let ht : IsTerminal t := MorphismProperty.Over.mkIdTerminal (@Etale) X
  let ht' : IsTerminal (F.obj t) := ht.isTerminalObj F
  have hcover : CoverPreserving X.smallEtaleTopology Y.smallEtaleTopology F :=
    Functor.isContinuous_iff_coverPreserving.mp inferInstance
  exact Functor.sheafPullback_isLocallyConstantWith F X.smallEtaleTopology
    Y.smallEtaleTopology D hcover ht ht' P G hG

/-- Inverse image along `f` sends finite locally constant étale sheaves of sets to
finite locally constant étale sheaves of sets. -/
theorem sheafPullback_isFiniteLocallyConstant
    [HasWeakSheafify Y.smallEtaleTopology (Type (u + 1))]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (Type (u + 1))]
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))]
    [∀ P : X.Etaleᵒᵖ ⥤ Type (u + 1), (smallEtalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (hF : Sheaf.IsFiniteLocallyConstant F) :
    Sheaf.IsFiniteLocallyConstant
      ((smallEtalePullback f).sheafPullback (Type (u + 1))
        X.smallEtaleTopology Y.smallEtaleTopology |>.obj F) :=
  by
  exact smallEtalePullback_isLocallyConstantWith f (Type (u + 1)) (fun A : Type (u + 1) ↦ Finite A) F hF

/-- Inverse image of finite locally constant étale sheaves of sets along `f : Y ⟶ X`. -/
noncomputable def finiteLocallyConstantPullback
    [HasWeakSheafify Y.smallEtaleTopology (Type (u + 1))]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (Type (u + 1))]
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))]
    [∀ P : X.Etaleᵒᵖ ⥤ Type (u + 1), (smallEtalePullback f).op.HasLeftKanExtension P] :
    (Sheaf.finiteLocallyConstant X.smallEtaleTopology).FullSubcategory ⥤
      (Sheaf.finiteLocallyConstant Y.smallEtaleTopology).FullSubcategory :=
  (Sheaf.finiteLocallyConstant Y.smallEtaleTopology).lift
    ((Sheaf.finiteLocallyConstant X.smallEtaleTopology).ι ⋙
      (smallEtalePullback f).sheafPullback (Type (u + 1))
        X.smallEtaleTopology Y.smallEtaleTopology)
    fun F ↦ sheafPullback_isFiniteLocallyConstant f F.obj F.property

/-- The set-level inverse-image functor is sheaf pullback on the underlying sheaf. -/
theorem finiteLocallyConstantPullback_obj
    [HasWeakSheafify Y.smallEtaleTopology (Type (u + 1))]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (Type (u + 1))]
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))]
    [∀ P : X.Etaleᵒᵖ ⥤ Type (u + 1), (smallEtalePullback f).op.HasLeftKanExtension P]
    (F : (Sheaf.finiteLocallyConstant X.smallEtaleTopology).FullSubcategory) :
    ((finiteLocallyConstantPullback f).obj F).obj =
      ((smallEtalePullback f).sheafPullback (Type (u + 1))
        X.smallEtaleTopology Y.smallEtaleTopology).obj F.obj :=
  sorry

/-- Inverse image along `f` sends finite locally constant étale sheaves of abelian groups
to finite locally constant étale sheaves of abelian groups. -/
theorem sheafPullback_isFiniteLocallyConstantAddCommGrp
    [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
    [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Sheaf.IsFiniteLocallyConstantAddCommGrp F) :
    Sheaf.IsFiniteLocallyConstantAddCommGrp
      ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u + 1}
        X.smallEtaleTopology Y.smallEtaleTopology |>.obj F) :=
  by
  exact smallEtalePullback_isLocallyConstantWith f (AddCommGrpCat.{u + 1}) (fun A : AddCommGrpCat.{u + 1} ↦ Finite A) F hF

/-- Inverse image of finite locally constant étale sheaves of abelian groups along `f`. -/
noncomputable def finiteLocallyConstantAddCommGrpPullback
    [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
    [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallEtalePullback f).op.HasLeftKanExtension P] :
    (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory ⥤
      (Sheaf.finiteLocallyConstantAddCommGrp Y.smallEtaleTopology).FullSubcategory :=
  (Sheaf.finiteLocallyConstantAddCommGrp Y.smallEtaleTopology).lift
    ((Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).ι ⋙
      (smallEtalePullback f).sheafPullback AddCommGrpCat.{u + 1}
        X.smallEtaleTopology Y.smallEtaleTopology)
    fun F ↦ sheafPullback_isFiniteLocallyConstantAddCommGrp f F.obj F.property

/-- The abelian inverse-image functor is sheaf pullback on the underlying sheaf. -/
theorem finiteLocallyConstantAddCommGrpPullback_obj
    [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
    [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (F : (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory) :
    ((finiteLocallyConstantAddCommGrpPullback f).obj F).obj =
      ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u + 1}
        X.smallEtaleTopology Y.smallEtaleTopology).obj F.obj :=
  sorry

variable (Λ : Type (u + 1)) [Ring Λ]

/-- Inverse image along `f` sends finite-type locally constant étale sheaves of `Λ`-modules
to finite-type locally constant étale sheaves of `Λ`-modules. -/
theorem sheafPullback_isFiniteTypeLocallyConstantModule
    [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Sheaf.IsFiniteTypeLocallyConstantModule F) :
    Sheaf.IsFiniteTypeLocallyConstantModule
      ((smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ)
        X.smallEtaleTopology Y.smallEtaleTopology |>.obj F) :=
  by
  letI : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} Λ) :=
    ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}
  exact smallEtalePullback_isLocallyConstantWith f (ModuleCat.{u + 1} Λ) (fun A : ModuleCat.{u + 1} Λ ↦ Module.Finite Λ A) F hF

/-- Inverse image of finite-type locally constant étale sheaves of `Λ`-modules along `f`. -/
noncomputable def finiteTypeLocallyConstantModulePullback
    [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P] :
    (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory ⥤
      (Sheaf.finiteTypeLocallyConstantModule Y.smallEtaleTopology Λ).FullSubcategory :=
  (Sheaf.finiteTypeLocallyConstantModule Y.smallEtaleTopology Λ).lift
    ((Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).ι ⋙
      (smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ)
        X.smallEtaleTopology Y.smallEtaleTopology)
    fun F ↦ sheafPullback_isFiniteTypeLocallyConstantModule f Λ F.obj F.property

/-- The module-valued inverse-image functor is sheaf pullback on the underlying sheaf. -/
theorem finiteTypeLocallyConstantModulePullback_obj
    [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    ((finiteTypeLocallyConstantModulePullback f Λ).obj F).obj =
      ((smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ)
        X.smallEtaleTopology Y.smallEtaleTopology).obj F.obj :=
  sorry

/-- Restriction of discrete modules along a continuous group homomorphism preserves the
open-stabilizer property. -/
theorem openStabilizer_res {R : Type v} [Ring R]
    {G H : Type u} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
    (φ : G →ₜ* H) (M : Action (ModuleCat.{max v u} R) H)
    (hM : openStabilizer R H M) :
    openStabilizer R G ((Action.res (ModuleCat.{max v u} R) φ.toMonoidHom).obj M) :=
  sorry

/-- Restriction of discrete continuous modules along a continuous group homomorphism. -/
noncomputable def discreteModuleRes {R : Type v} [Ring R]
    {G H : Type u} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
    (φ : G →ₜ* H) :
    DiscreteModuleCat R H ⥤ DiscreteModuleCat R G :=
  (openStabilizer R G).lift
    ((openStabilizer R H).ι ⋙ Action.res (ModuleCat.{max v u} R) φ.toMonoidHom)
    fun M ↦ openStabilizer_res φ M.obj M.property


end AlgebraicGeometry.Scheme
