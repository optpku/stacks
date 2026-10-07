module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.FreeAbelian
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Presheaf
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import stacks_project.Chap85.Lemma_85_15_1
public import stacks_project.Chap85.Lemma_85_16_2_Comparison
public import stacks_project.Chap85.Lemma_85_17_2_Hom

/-!
# Čech cochain of `a⁻¹ F` along a hypercovering

The unaugmented cosimplicial abelian sheaf `n ↦ j_{n,*} j_n⁻¹ F` attached to a
site-level hypercovering, its alternating-coface complex, and the canonical
comparison morphism from `Hom(s(Z_{F(K)^#}), F)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open CategoryTheory.GrothendieckTopology.SemiRepresentableLocalization
open FormalCoproduct
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [HasEqualizers C] [HasPullbacks C]
variable (K : HypercoveringOf.Terminal.{w} J)
variable [HasWeakSheafify J AddCommGrpCat.{max w u v}]
variable [HasWeakSheafify J (Type (max w u v))]
variable [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max w u v})]
variable [∀ n : SimplexCategory,
    ∀ P : (OverSite (K.simplicial.obj (op n)))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
      (forget (K.simplicial.obj (op n))).op.HasPointwiseRightKanExtension P]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ∀ P : (OverSite (K.simplicial.obj (op n)))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
      (overMap (K.simplicial.map φ.op)).op.HasPointwiseRightKanExtension P]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ∀ P : (OverSite (K.simplicial.obj (op n)))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
      (overMap (K.simplicial.map φ.op) ⋙
          forget (K.simplicial.obj (op m))).op.HasPointwiseRightKanExtension P]

/-- Inverse image `a_n⁻¹` along localization at `K_n`, as continuous sheaf pushforward of
`forget (K_n)`. -/
def abelianStageInverseImage (n : SimplexCategory) :
    Sheaf J AddCommGrpCat.{max w u v} ⥤
      Sheaf (overTopology J (K.simplicial.obj (op n))) AddCommGrpCat.{max w u v} :=
  -- Local instance justification (search instability): `IsContinuous` of `j_n` is keyed by topologies whose ambient `J` is not an outParam, so `forget_isContinuous` is not found by instance search at use sites.
  letI := forget_isContinuous J (K.simplicial.obj (op n))
  (forget (K.simplicial.obj (op n))).sheafPushforwardContinuous
    AddCommGrpCat.{max w u v} (overTopology J (K.simplicial.obj (op n))) J

/-- Relocalization `C / K_n ⥤ C / K_m` induced by a simplex operator `φ : m ⟶ n`. -/
abbrev overSiteMap {m n : SimplexCategory} (φ : m ⟶ n) :
    OverSite (K.simplicial.obj (op n)) ⥤ OverSite (K.simplicial.obj (op m)) :=
  overMap (K.simplicial.map φ.op)

/-- Relocalization along `φ` followed by `j_m` recovers `j_n`. -/
def overSiteMap_forget {m n : SimplexCategory} (φ : m ⟶ n) :
    overSiteMap J K φ ⋙ forget (K.simplicial.obj (op m)) ≅
      forget (K.simplicial.obj (op n)) :=
  overMap_forget (K.simplicial.map φ.op)

/-- Direct image along relocalization `overSiteMap φ`. -/
def abelianFacePushforwardMap {m n : SimplexCategory} (φ : m ⟶ n) :
    Sheaf (overTopology J (K.simplicial.obj (op n))) AddCommGrpCat.{max w u v} ⥤
      Sheaf (overTopology J (K.simplicial.obj (op m))) AddCommGrpCat.{max w u v} :=
  (overSiteMap J K φ).sheafPushforwardCocontinuous
    AddCommGrpCat.{max w u v}
    (overTopology J (K.simplicial.obj (op n)))
    (overTopology J (K.simplicial.obj (op m)))

/-- Inverse image along relocalization `overSiteMap φ`. -/
def abelianFaceInverseImageMap {m n : SimplexCategory} (φ : m ⟶ n) :
    Sheaf (overTopology J (K.simplicial.obj (op m))) AddCommGrpCat.{max w u v} ⥤
      Sheaf (overTopology J (K.simplicial.obj (op n))) AddCommGrpCat.{max w u v} :=
  (overSiteMap J K φ).sheafPushforwardContinuous
    AddCommGrpCat.{max w u v}
    (overTopology J (K.simplicial.obj (op n)))
    (overTopology J (K.simplicial.obj (op m)))

/-- Adjunction `v⁻¹ ⊣ v_*` for relocalization along a simplex operator. -/
def abelianFaceAdjunctionMap {m n : SimplexCategory} (φ : m ⟶ n) :
    abelianFaceInverseImageMap J K φ ⊣ abelianFacePushforwardMap J K φ :=
  (overSiteMap J K φ).sheafAdjunctionCocontinuous
    AddCommGrpCat.{max w u v}
    (overTopology J (K.simplicial.obj (op n)))
    (overTopology J (K.simplicial.obj (op m)))

/-- Inverse-image identification `a_n⁻¹ ≅ a_m⁻¹ ⋙ v⁻¹`. -/
def abelianStageInverseImage_comp {m n : SimplexCategory} (φ : m ⟶ n) :
    abelianStageInverseImage J K m ⋙ abelianFaceInverseImageMap J K φ ≅
      abelianStageInverseImage J K n :=
  Functor.sheafPushforwardContinuousComp' (overSiteMap_forget J K φ)
    AddCommGrpCat.{max w u v}
    (overTopology J (K.simplicial.obj (op n)))
    (overTopology J (K.simplicial.obj (op m))) J

/-- Direct-image identification `v_* ⋙ j_{m,*} ≅ j_{n,*}`. -/
def abelianFace_comp_stagePushforwardMap {m n : SimplexCategory} (φ : m ⟶ n) :
    abelianFacePushforwardMap J K φ ⋙
        abelianStagePushforward J K.simplicial m ≅
      abelianStagePushforward J K.simplicial n :=
  Functor.sheafPushforwardCocontinuousComp'
    (overTopology J (K.simplicial.obj (op n)))
    (overTopology J (K.simplicial.obj (op m))) J
    (overSiteMap J K φ) (forget (K.simplicial.obj (op m)))
    (overSiteMap_forget J K φ)

/-- The structure map `j_{m,*} j_m⁻¹ F ⟶ j_{n,*} j_n⁻¹ F` induced by `φ : m ⟶ n`. -/
def abelianStagePushforward_map (F : Sheaf J AddCommGrpCat.{max w u v})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (abelianStagePushforward J K.simplicial m).obj
        ((abelianStageInverseImage J K m).obj F) ⟶
      (abelianStagePushforward J K.simplicial n).obj
        ((abelianStageInverseImage J K n).obj F) :=
  (abelianStagePushforward J K.simplicial m).map
      ((abelianFaceAdjunctionMap J K φ).unit.app
        ((abelianStageInverseImage J K m).obj F)) ≫
    (abelianStagePushforward J K.simplicial m).map
      ((abelianFacePushforwardMap J K φ).map
        ((abelianStageInverseImage_comp J K φ).hom.app F)) ≫
    (abelianFace_comp_stagePushforwardMap J K φ).hom.app
      ((abelianStageInverseImage J K n).obj F)

/-- Identity simplex operators act as identity on push-pull. -/
theorem abelianStagePushforward_map_id (F : Sheaf J AddCommGrpCat.{max w u v})
    (n : SimplexCategory) :
    abelianStagePushforward_map J K F (𝟙 n) = 𝟙 _ :=
  sorry

/-- Structure maps of push-pull respect composition of simplex operators. -/
theorem abelianStagePushforward_map_comp (F : Sheaf J AddCommGrpCat.{max w u v})
    {m n p : SimplexCategory} (φ : m ⟶ n) (ψ : n ⟶ p) :
    abelianStagePushforward_map J K F (φ ≫ ψ) =
      abelianStagePushforward_map J K F φ ≫ abelianStagePushforward_map J K F ψ :=
  sorry

/-- The cosimplicial abelian sheaf `n ↦ j_{n,*} j_n⁻¹ F`. -/
def cechCosimplicial (F : Sheaf J AddCommGrpCat.{max w u v}) :
    CosimplicialObject (Sheaf J AddCommGrpCat.{max w u v}) where
  obj n :=
    (abelianStagePushforward J K.simplicial n).obj
      ((abelianStageInverseImage J K n).obj F)
  map φ := abelianStagePushforward_map J K F φ
  map_id n := abelianStagePushforward_map_id J K F n
  map_comp φ ψ := abelianStagePushforward_map_comp J K F φ ψ

/-- Face maps of `cechCosimplicial` are the structure maps of `K`. -/
theorem cechCosimplicial_map (F : Sheaf J AddCommGrpCat.{max w u v})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (cechCosimplicial J K F).map φ = abelianStagePushforward_map J K F φ :=
  sorry

/-- The unaugmented Čech cochain `j_{0,*} j_0⁻¹ F → j_{1,*} j_1⁻¹ F → ⋯`. -/
def cechComplex (F : Sheaf J AddCommGrpCat.{max w u v}) :
    CochainComplex (Sheaf J AddCommGrpCat.{max w u v}) ℕ :=
  (alternatingCofaceMapComplex _).obj (cechCosimplicial J K F)

/-- Degree `n` of `cechComplex` is `j_{n,*} j_n⁻¹ F`. -/
theorem cechComplex_X (F : Sheaf J AddCommGrpCat.{max w u v}) (n : ℕ) :
    (cechComplex J K F).X n =
      (abelianStagePushforward J K.simplicial ⦋n⦌).obj
        ((abelianStageInverseImage J K ⦋n⦌).obj F) :=
  sorry

/-- The sheafification unit of the free abelian presheaf on `F(K_n)`, evaluated at `V`. -/
def homToCech_toSheafify (n : ℕ) (V : Cᵒᵖ) :
    (FreeAbelianPresheaf.obj ((hypercoveringPresheafULift J K).obj (op ⦋n⦌))).obj V ⟶
      ((freeAbelianComplex J K).X n).obj.obj V :=
  ((sheafificationAdjunction J AddCommGrpCat.{max w u v}).unit.app
      (FreeAbelianPresheaf.obj ((hypercoveringPresheafULift J K).obj (op ⦋n⦌)))).app V

/-- Canonical generator of `F(K_n)` at the source of a localization object `U`. -/
def homToCech_generator (n : ℕ) (U : OverSite (K.simplicial.obj (op ⦋n⦌))) :
    ((hypercoveringPresheafULift J K).obj (op ⦋n⦌)).obj
      (op ((forget (K.simplicial.obj (op ⦋n⦌))).obj U)) :=
  ULift.up
    (toPresheafObjMk (K.simplicial.obj (op ⦋n⦌))
      (op ((forget (K.simplicial.obj (op ⦋n⦌))).obj U)) U.1 U.2.hom)

/-- Image of `homToCech_generator` in the free abelian sheaf `Z_{F(K_n)}`. -/
def homToCech_generatorFree (n : ℕ) (U : OverSite (K.simplicial.obj (op ⦋n⦌))) :
    (CategoryTheory.forget AddCommGrpCat.{max w u v}).obj
      (((freeAbelianComplex J K).X n).obj.obj
        (op ((forget (K.simplicial.obj (op ⦋n⦌))).obj U))) :=
  (CategoryTheory.forget AddCommGrpCat.{max w u v}).map
      (homToCech_toSheafify J K n
        (op ((forget (K.simplicial.obj (op ⦋n⦌))).obj U)))
    (FreeAbelianGroup.of (homToCech_generator J K n U))

/-- Evaluation of a local Hom at the canonical generator of `K_n` at `U`. -/
def homToCech_evalApp (F : Sheaf J AddCommGrpCat.{max w u v}) (n : ℕ)
    (U : (OverSite (K.simplicial.obj (op ⦋n⦌)))ᵒᵖ) :
    ((abelianStageInverseImage J K ⦋n⦌).obj ((homComplex J K F).X n)).obj.obj U ⟶
      ((abelianStageInverseImage J K ⦋n⦌).obj F).obj.obj U :=
  AddCommGrpCat.ofHom
    { toFun := fun α ↦
        (CategoryTheory.forget AddCommGrpCat.{max w u v}).map
            (α.app (op (CategoryTheory.Over.mk
              (CategoryTheory.CategoryStruct.id
                ((forget (K.simplicial.obj (op ⦋n⦌))).obj U.unop)))))
          (homToCech_generatorFree J K n U.unop)
      map_zero' := sorry
      map_add' := sorry }

/-- Naturality of generator evaluation in the localization site. -/
theorem homToCech_evalApp_naturality (F : Sheaf J AddCommGrpCat.{max w u v}) (n : ℕ)
    {U U' : (OverSite (K.simplicial.obj (op ⦋n⦌)))ᵒᵖ} (f : U ⟶ U') :
    ((abelianStageInverseImage J K ⦋n⦌).obj ((homComplex J K F).X n)).obj.map f ≫
        homToCech_evalApp J K F n U' =
      homToCech_evalApp J K F n U ≫
        ((abelianStageInverseImage J K ⦋n⦌).obj F).obj.map f :=
  sorry

/-- Inverse image of `Hom(Z_{F(K_n)}, F)` evaluates onto inverse image of `F`. -/
def homToCech_eval (F : Sheaf J AddCommGrpCat.{max w u v}) (n : ℕ) :
    (abelianStageInverseImage J K ⦋n⦌).obj ((homComplex J K F).X n) ⟶
      (abelianStageInverseImage J K ⦋n⦌).obj F where
  hom :=
    { app := fun U ↦ homToCech_evalApp J K F n U
      naturality := fun _ _ f ↦ homToCech_evalApp_naturality J K F n f }

/-- Degreewise comparison `Hom(Z_{F(K_n)}, F) ⟶ j_{n,*} j_n⁻¹ F` as the adjunct of
generator evaluation. -/
def homToCech_f (F : Sheaf J AddCommGrpCat.{max w u v}) (n : ℕ) :
    (homComplex J K F).X n ⟶ (cechComplex J K F).X n :=
  -- Local instance justification (search instability): `IsContinuous` of `j_n` is keyed by topologies whose ambient `J` is not an outParam, so `forget_isContinuous` is not found by instance search at use sites.
  letI := forget_isContinuous J (K.simplicial.obj (op ⦋n⦌))
  ((forget (K.simplicial.obj (op ⦋n⦌))).sheafAdjunctionCocontinuous
      AddCommGrpCat.{max w u v}
      (overTopology J (K.simplicial.obj (op ⦋n⦌))) J).homEquiv
    ((homComplex J K F).X n)
    ((abelianStageInverseImage J K ⦋n⦌).obj F)
    (homToCech_eval J K F n)

/-- Differentials intertwine the degreewise Hom-to-Čech comparison. -/
theorem homToCech_comm (F : Sheaf J AddCommGrpCat.{max w u v}) (i j : ℕ)
    (hij : (ComplexShape.up ℕ).Rel i j) :
    homToCech_f J K F i ≫ (cechComplex J K F).d i j =
      (homComplex J K F).d i j ≫ homToCech_f J K F j :=
  sorry

/-- The canonical comparison morphism identifying `Hom(s(Z_{F(K)^#}), F)` with the
unaugmented Čech cochain of `a⁻¹ F`. -/
def homToCech (F : Sheaf J AddCommGrpCat.{max w u v}) :
    homComplex J K F ⟶ cechComplex J K F where
  f n := homToCech_f J K F n
  comm' i j hij := homToCech_comm J K F i j hij

end CategoryTheory.SemiRepresentableFamily

