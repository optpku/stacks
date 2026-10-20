module
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Basic
public import ReasLib.CategoryTheory.Sites.Pullback.SliceComparison
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
universe u v u' v' w z
namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [F.IsContinuous J K] [HasBinaryProducts C] [HasBinaryProducts D] [HasPullbacks D]
variable [PreservesLimitsOfShape (Discrete WalkingPair) F]
variable (A : Type w) [Category.{z} A]
variable [HasWeakSheafify J A] [HasWeakSheafify K A]
variable [∀ V : C, HasWeakSheafify (J.over V) A]
variable [∀ U : D, HasWeakSheafify (K.over U) A]
variable [∀ V : C, (Over.post F).IsContinuous (J.over V) (K.over (F.obj V))]
variable [∀ Q : Cᵒᵖ ⥤ A, F.op.HasLeftKanExtension Q]
variable [∀ Q : Cᵒᵖ ⥤ A, F.op.HasPointwiseLeftKanExtension Q]
variable [∀ V : C, ∀ Q : (Over V)ᵒᵖ ⥤ A, (Over.post F).op.HasLeftKanExtension Q]
variable [∀ V : C, ∀ Q : (Over V)ᵒᵖ ⥤ A, (Over.post F).op.HasPointwiseLeftKanExtension Q]
variable [∀ U : D, ∀ Q : (Over U)ᵒᵖ ⥤ A, (Over.forget U).op.HasPointwiseRightKanExtension Q]
variable [∀ U V : D, ∀ g : U ⟶ V, ∀ Q : (Over U)ᵒᵖ ⥤ A,
    (Over.map g).op.HasPointwiseRightKanExtension Q]
variable (hcover : CoverPreserving J K F)
variable {t : C} (ht : IsTerminal t) (ht' : IsTerminal (F.obj t))

include ht ht' hcover in
/-- The given local constant charts pull back to concrete charts with the same models. -/
theorem sheafPullback_isLocallyConstantWith (P : A → Prop) (G : Sheaf J A)
    (hG : Sheaf.IsLocallyConstantWith (J := J) P G) :
    Sheaf.IsLocallyConstantWith (J := K) P ((F.sheafPullback A J K).obj G) := by
  classical
  letI := hG
  obtain ⟨I, Z, hZ, models⟩ :=
    Sheaf.IsLocallyConstantWith.existsConstantCover (P := P) (F := G) t
  refine ⟨fun U ↦ ?_⟩
  let charts (i : I) : Over U :=
    (Over.pullback (ht'.from U)).obj ((Over.post F).obj (Z i))
  refine ⟨I, charts, ?_, ?_⟩
  · have covers : IsTerminal t → CoverPreserving J K F →
        (J.over t).CoversTop Z → (K.over U).CoversTop charts := sorry
    exact covers ht hcover hZ
  · intro i
    obtain ⟨E, hE, ⟨e⟩⟩ := models i
    let g : (charts i).left ⟶ F.obj (Z i).left :=
      pullback.fst (F.map (Z i).hom) (ht'.from U)
    let e' := pulledConstantChartIso F J K A (Z i).left G E e
    refine ⟨E, hE, ⟨?_⟩⟩
    exact (((F.sheafPullback A J K).obj G).pushforwardOverMapIso g).symm ≪≫
      ((Over.map g).sheafPushforwardContinuous A
        (K.over (charts i).left) (K.over (F.obj (Z i).left))).mapIso e' ≪≫
      (constantSheafRestrictionIso (Over.map g)
        (K.over (charts i).left) (K.over (F.obj (Z i).left)) A).app E

end CategoryTheory.Functor
