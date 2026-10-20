module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import ReasLib.CategoryTheory.Sites.Family.Simplicial.Augmentation

/-!
# Degreewise inverse image and abelian equalizer comparison for total localization

Fiber inclusion `ι` composed with `j_total` recovers the stage localization `j_n`. Inverse
image along `j_total` therefore restricts in degree `n` to inverse image along `j_n`. Direct
image `a_*` of an abelian sheaf compares to the equalizer of `j_{0,*} G_0 ⇉ j_{1,*} G_1`.
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.GrothendieckTopology.SemiRepresentableLocalization
open scoped Simplicial

noncomputable section

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (K : SimplicialObject (FormalCoproduct.{w} C))

/-- The fiber inclusion `ι` of `(C / K)_total` at degree `n` is continuous. -/
instance overSite_ι_isContinuous (n : SimplexCategory) :
    (Grothendieck.ι (overSiteDiagram K) (op n)).IsContinuous
      (overTopology J (K.obj (op n))) (overSiteTotalTopology J K) :=
  sorry

/-- The fiber inclusion `ι` of `(C / K)_total` at degree `n` is cocontinuous. -/
instance overSite_ι_isCocontinuous (n : SimplexCategory) :
    (Grothendieck.ι (overSiteDiagram K) (op n)).IsCocontinuous
      (overTopology J (K.obj (op n))) (overSiteTotalTopology J K) :=
  sorry

/-- The identity components comparing fiber localization with stage localization are natural. -/
private theorem fiber_comp_totalForget_naturality (n : SimplexCategory)
    {X Y : OverSite (K.obj (op n))} (f : X ⟶ Y) :
    (Grothendieck.ι (overSiteDiagram K) (op n) ⋙ totalForget K).map f ≫
        (Iso.refl ((forget (K.obj (op n))).obj Y)).hom =
      (Iso.refl ((forget (K.obj (op n))).obj X)).hom ≫
        (forget (K.obj (op n))).map f :=
  sorry

-- The public isomorphism uses a private naturality proof.
set_option backward.privateInPublic true in
/-- Fiber inclusion into `(C / K)_total` followed by `j_total` is localization at `K_n`. -/
def fiber_comp_totalForget (n : SimplexCategory) :
    Grothendieck.ι (overSiteDiagram K) (op n) ⋙ totalForget K ≅ forget (K.obj (op n)) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by exact fiber_comp_totalForget_naturality K n)

/-- The composite `ι ⋙ j_total` is continuous, by transport from `j_n`. -/
instance fiber_comp_isContinuous (n : SimplexCategory) :
    (Grothendieck.ι (overSiteDiagram K) (op n) ⋙ totalForget K).IsContinuous
      (overTopology J (K.obj (op n))) J :=
  Functor.isContinuous_of_iso (fiber_comp_totalForget K n).symm
    (overTopology J (K.obj (op n))) J

/-- Restriction of a total sheaf to the degree-`n` stage, as inverse image along `ι`. -/
def sheafFiberRestrict (n : SimplexCategory) :
    Sheaf (overSiteTotalTopology J K) (Type (max w u v)) ⥤
      Sheaf (overTopology J (K.obj (op n))) (Type (max w u v)) :=
  (Grothendieck.ι (overSiteDiagram K) (op n)).sheafPushforwardContinuous
    (Type (max w u v)) (overTopology J (K.obj (op n))) (overSiteTotalTopology J K)

/-- Restriction of an abelian total sheaf to the degree-`n` stage. -/
def abelianFiberRestrict (n : SimplexCategory) :
    Sheaf (overSiteTotalTopology J K) AddCommGrpCat.{max w u v} ⥤
      Sheaf (overTopology J (K.obj (op n))) AddCommGrpCat.{max w u v} :=
  (Grothendieck.ι (overSiteDiagram K) (op n)).sheafPushforwardContinuous
    AddCommGrpCat.{max w u v} (overTopology J (K.obj (op n))) (overSiteTotalTopology J K)

/-- Inverse image `a_n⁻¹` along localization at `K_n`. -/
def sheafStageRestrict (n : SimplexCategory) :
    Sheaf J (Type (max w u v)) ⥤
      Sheaf (overTopology J (K.obj (op n))) (Type (max w u v)) :=
  by
    apply Functor.sheafPushforwardContinuous (F := forget (K.obj (op n)))
      (A := Type (max w u v))

/-- Inverse image along `j_total` restricts in degree `n` to inverse image along `j_n`. -/
def sheafInverseImage_fiberRestrict (n : SimplexCategory) :
    (totalForget K).sheafPushforwardContinuous (Type (max w u v))
        (overSiteTotalTopology J K) J ⋙ sheafFiberRestrict J K n ≅
      sheafStageRestrict J K n :=
  by
    apply (config := { allowSynthFailures := true }) Functor.sheafPushforwardContinuousComp'
    exact fiber_comp_totalForget K n

/-- Direct image `j_{n,*}` of abelian sheaves along localization at `K_n`. -/
abbrev abelianStagePushforward (n : SimplexCategory)
    [∀ P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
      (forget (K.obj (op n))).op.HasPointwiseRightKanExtension P] :
    Sheaf (overTopology J (K.obj (op n))) AddCommGrpCat.{max w u v} ⥤
      Sheaf J AddCommGrpCat.{max w u v} :=
  (forget (K.obj (op n))).sheafPushforwardCocontinuous
    AddCommGrpCat.{max w u v} (overTopology J (K.obj (op n))) J

/-- Direct image `a_*` of abelian sheaves along `j_total`. -/
abbrev abelianTotalPushforward
    [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
      (totalForget K).op.HasPointwiseRightKanExtension P] :
    Sheaf (overSiteTotalTopology J K) AddCommGrpCat.{max w u v} ⥤
      Sheaf J AddCommGrpCat.{max w u v} :=
  (totalForget K).sheafPushforwardCocontinuous
    AddCommGrpCat.{max w u v} (overSiteTotalTopology J K) J

/-- The coface operator `δ i` as relocalization `C / K_1 ⥤ C / K_0`. -/
abbrev overSiteFace (i : Fin 2) :
    OverSite (K.obj (op ⦋1⦌)) ⥤ OverSite (K.obj (op ⦋0⦌)) :=
  overMap (K.map (SimplexCategory.δ i).op)

/-- Relocalization along `δ i` followed by `j_0` recovers `j_1`. -/
def overSiteFace_forget (i : Fin 2) :
    overSiteFace K i ⋙ forget (K.obj (op ⦋0⦌)) ≅ forget (K.obj (op ⦋1⦌)) :=
  overMap_forget (K.map (SimplexCategory.δ i).op)

/-- The Grothendieck natural transformation of a coface, as a map of fiber inclusions. -/
def overSiteFace_ιNatTrans (i : Fin 2) :
    Grothendieck.ι (overSiteDiagram K) (op ⦋1⦌) ⟶
      overSiteFace K i ⋙ Grothendieck.ι (overSiteDiagram K) (op ⦋0⦌) :=
  Grothendieck.ιNatTrans (SimplexCategory.δ i).op

/-- The composite `f_{δ i} ⋙ ι_0` is continuous. -/
instance overSiteFace_comp_ι_isContinuous (i : Fin 2) :
    (overSiteFace K i ⋙ Grothendieck.ι (overSiteDiagram K) (op ⦋0⦌)).IsContinuous
      (overTopology J (K.obj (op ⦋1⦌))) (overSiteTotalTopology J K) :=
  by
    apply (config := { allowSynthFailures := true }) Functor.isContinuous_comp
      (K := overTopology J (K.obj (op ⦋0⦌)))
    exact overSite_ι_isContinuous J K ⦋0⦌

variable [h_totalRan :
    ∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
      (totalForget K).op.HasPointwiseRightKanExtension P]
variable [h_forgetRan :
    ∀ (n : SimplexCategory) (P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ AddCommGrpCat.{max w u v}),
      (forget (K.obj (op n))).op.HasPointwiseRightKanExtension P]
variable [h_ιRan :
    ∀ (n : SimplexCategory) (P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ AddCommGrpCat.{max w u v}),
      (Grothendieck.ι (overSiteDiagram K) (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (i : Fin 2) (P : (OverSite (K.obj (op ⦋1⦌)))ᵒᵖ ⥤ AddCommGrpCat.{max w u v}),
  (overSiteFace K i).op.HasPointwiseRightKanExtension P]
variable [∀ (i : Fin 2) (P : (OverSite (K.obj (op ⦋1⦌)))ᵒᵖ ⥤ AddCommGrpCat.{max w u v}),
  (overSiteFace K i ⋙ forget (K.obj (op ⦋0⦌))).op.HasPointwiseRightKanExtension P]

/-- Direct image along fiber inclusion `ι`, dual to `abelianFiberRestrict`. -/
def abelianFiberPushforward (n : SimplexCategory) :
    Sheaf (overTopology J (K.obj (op n))) AddCommGrpCat.{max w u v} ⥤
      Sheaf (overSiteTotalTopology J K) AddCommGrpCat.{max w u v} :=
  (Grothendieck.ι (overSiteDiagram K) (op n)).sheafPushforwardCocontinuous
    AddCommGrpCat.{max w u v} (overTopology J (K.obj (op n))) (overSiteTotalTopology J K)

/-- Inverse image along the coface `overSiteFace i`. -/
def abelianFaceInverseImageFunctor (i : Fin 2) :
    Sheaf (overTopology J (K.obj (op ⦋0⦌))) AddCommGrpCat.{max w u v} ⥤
      Sheaf (overTopology J (K.obj (op ⦋1⦌))) AddCommGrpCat.{max w u v} :=
  (overSiteFace K i).sheafPushforwardContinuous AddCommGrpCat.{max w u v}
    (overTopology J (K.obj (op ⦋1⦌))) (overTopology J (K.obj (op ⦋0⦌)))

/-- Direct image along the coface `overSiteFace i`. -/
def abelianFacePushforward (i : Fin 2) :
    Sheaf (overTopology J (K.obj (op ⦋1⦌))) AddCommGrpCat.{max w u v} ⥤
      Sheaf (overTopology J (K.obj (op ⦋0⦌))) AddCommGrpCat.{max w u v} :=
  (overSiteFace K i).sheafPushforwardCocontinuous AddCommGrpCat.{max w u v}
    (overTopology J (K.obj (op ⦋1⦌))) (overTopology J (K.obj (op ⦋0⦌)))

/-- Cocontinuous adjunction of the coface `overSiteFace i`. -/
def abelianFaceAdjunction (i : Fin 2) :
    abelianFaceInverseImageFunctor J K i ⊣ abelianFacePushforward J K i :=
  (overSiteFace K i).sheafAdjunctionCocontinuous AddCommGrpCat.{max w u v}
    (overTopology J (K.obj (op ⦋1⦌))) (overTopology J (K.obj (op ⦋0⦌)))

set_option backward.privateInPublic true in
/-- Restriction along `overSiteFace i ⋙ ι_0`. -/
private def abelianFaceCompFiberRestrict (i : Fin 2) :
    Sheaf (overSiteTotalTopology J K) AddCommGrpCat.{max w u v} ⥤
      Sheaf (overTopology J (K.obj (op ⦋1⦌))) AddCommGrpCat.{max w u v} :=
  (overSiteFace K i ⋙ Grothendieck.ι (overSiteDiagram K) (op ⦋0⦌)).sheafPushforwardContinuous
    AddCommGrpCat.{max w u v} (overTopology J (K.obj (op ⦋1⦌))) (overSiteTotalTopology J K)

set_option backward.privateInPublic true in
/-- `ι_0⁻¹ ⋙ f_{δ i}⁻¹ ≅ (f_{δ i} ⋙ ι_0)⁻¹`. -/
private def abelianFace_comp_fiberRestrict (i : Fin 2) :
    abelianFiberRestrict J K ⦋0⦌ ⋙ abelianFaceInverseImageFunctor J K i ≅
      abelianFaceCompFiberRestrict J K i :=
  Iso.refl _

-- The public transition uses the private restriction-composition identification.
set_option backward.privateInPublic true in
/-- Inverse-image form of the coface transition: `f_{δ i}⁻¹ G_0 ⟶ G_1`. -/
def abelianFaceInverseImage
    (G : Sheaf (overSiteTotalTopology J K) AddCommGrpCat.{max w u v}) (i : Fin 2) :
    (abelianFaceInverseImageFunctor J K i).obj ((abelianFiberRestrict J K ⦋0⦌).obj G) ⟶
      (abelianFiberRestrict J K ⦋1⦌).obj G :=
  by
    exact (abelianFace_comp_fiberRestrict J K i).hom.app G ≫
      ⟨Functor.whiskerRight (NatTrans.op (overSiteFace_ιNatTrans K i)) G.obj⟩

/-- Direct-image identification `f_{δ i,*} ⋙ j_{0,*} ≅ j_{1,*}`. -/
def abelianFace_comp_stagePushforward (i : Fin 2) :
    abelianFacePushforward J K i ⋙ abelianStagePushforward J K ⦋0⦌ ≅
      abelianStagePushforward J K ⦋1⦌ :=
  Functor.sheafPushforwardCocontinuousComp'
    (overTopology J (K.obj (op ⦋1⦌)))
    (overTopology J (K.obj (op ⦋0⦌))) J
    (overSiteFace K i) (forget (K.obj (op ⦋0⦌)))
    (overSiteFace_forget K i)

/-- Direct-image identification `ι_{n,*} ⋙ a_* ≅ j_{n,*}`. -/
def abelianFiber_comp_totalPushforward (n : SimplexCategory) :
    abelianFiberPushforward J K n ⋙ abelianTotalPushforward J K ≅
      abelianStagePushforward J K n :=
  by
    apply (config := { allowSynthFailures := true }) Functor.sheafPushforwardCocontinuousComp'
    exact fiber_comp_totalForget K n


/-- The two maps `j_{0,*} G_0 ⇉ j_{1,*} G_1` induced by the coface operators `δ i`. -/
def abelianPushforwardParallel
    (G : Sheaf (overSiteTotalTopology J K) AddCommGrpCat.{max w u v}) (i : Fin 2) :
    (abelianStagePushforward J K ⦋0⦌).obj ((abelianFiberRestrict J K ⦋0⦌).obj G) ⟶
      (abelianStagePushforward J K ⦋1⦌).obj ((abelianFiberRestrict J K ⦋1⦌).obj G) :=
  (abelianStagePushforward J K ⦋0⦌).map
      ((abelianFaceAdjunction J K i).unit.app ((abelianFiberRestrict J K ⦋0⦌).obj G)) ≫
    (abelianStagePushforward J K ⦋0⦌).map
      ((abelianFacePushforward J K i).map (abelianFaceInverseImage J K G i)) ≫
    (abelianFace_comp_stagePushforward J K i).hom.app
      ((abelianFiberRestrict J K ⦋1⦌).obj G)

/-- The comparison `a_* G ⟶ j_{0,*} G_0`. -/
def abelianPushforwardι
    (G : Sheaf (overSiteTotalTopology J K) AddCommGrpCat.{max w u v}) :
    (abelianTotalPushforward J K).obj G ⟶
      (abelianStagePushforward J K ⦋0⦌).obj ((abelianFiberRestrict J K ⦋0⦌).obj G) :=
  (abelianTotalPushforward J K).map
      ({ hom :=
          ((Grothendieck.ι (overSiteDiagram K) (op ⦋0⦌)).op.ranAdjunction
              AddCommGrpCat.{max w u v}).unit.app G.obj } :
        G ⟶ (abelianFiberPushforward J K ⦋0⦌).obj ((abelianFiberRestrict J K ⦋0⦌).obj G)) ≫
    (abelianFiber_comp_totalPushforward J K ⦋0⦌).hom.app
      ((abelianFiberRestrict J K ⦋0⦌).obj G)

/-- The degree-zero restriction comparison equalizes the two coface maps. -/
theorem abelianPushforward_equalizes
    (G : Sheaf (overSiteTotalTopology J K) AddCommGrpCat.{max w u v}) :
    abelianPushforwardι J K G ≫ abelianPushforwardParallel J K G 0 =
      abelianPushforwardι J K G ≫ abelianPushforwardParallel J K G 1 :=
  sorry

variable [HasEqualizers (Sheaf J AddCommGrpCat.{max w u v})]

/-- The comparison of `a_* G` into the equalizer of `j_{0,*} G_0 ⇉ j_{1,*} G_1`. -/
def abelianPushforwardToEqualizer
    (G : Sheaf (overSiteTotalTopology J K) AddCommGrpCat.{max w u v}) :
    (abelianTotalPushforward J K).obj G ⟶
      equalizer (abelianPushforwardParallel J K G 0) (abelianPushforwardParallel J K G 1) :=
  equalizer.lift (abelianPushforwardι J K G) (abelianPushforward_equalizes J K G)

/-- The canonical direct-image comparison with the equalizer of the two coface maps is
an isomorphism. -/
instance abelianPushforwardToEqualizer_isIso
    (G : Sheaf (overSiteTotalTopology J K) AddCommGrpCat.{max w u v}) :
    IsIso (abelianPushforwardToEqualizer J K G) :=
  sorry

end CategoryTheory.SemiRepresentableFamily
