/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.Basic
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import stacks_project.Chap85.Lemma_85_15_1_Site
public import stacks_project.Chap85.Lemma_85_15_2_Localization
public import stacks_project.Chap85.Lemma_85_3_2_Total
public import stacks_project.Chap85.Situation_85_3_3_Fiberwise
import StacksCheckRecall

/- The category of semi-representable objects over X is OverFamily X,
i.e. SR(C, X) = SR(C/X), and constructions on C apply to the slice site
given by J.over X. -/
@[stacks 0D8C] #check @CategoryTheory.SemiRepresentableFamily.OverFamily
@[stacks 0D8C] #check @CategoryTheory.GrothendieckTopology.over

/- Remark 85.16.4 (Variant for over an object) (1): instantiating the case-B
total site of n ↦ OverSite (K.obj n) on Over X yields (C/K)_total for a
simplicial object K of OverFamily X. -/
@[stacks 0D8C] #check @CategoryTheory.Grothendieck.precoverage
@[stacks 0D8C] #check @CategoryTheory.Grothendieck.topology

/- Remark 85.16.4 (Variant for over an object) (2): the localization functor
j_total : (C/K)_total ⥤ Over X is assembled by Grothendieck.functorFrom from
the compatible family forget : OverSite K_n ⥤ Over X. -/
@[stacks 0D8C] #check @CategoryTheory.Grothendieck.functorFrom

/- Remark 85.16.4 (Variant for over an object) (3): the localization functors
j_n : C/K_n ⥤ Over X are SemiRepresentableFamily.forget instantiated on Over X. -/
@[stacks 0D8C] #check @CategoryTheory.SemiRepresentableFamily.forget

/- Remark 85.16.4 (Variant for over an object) (4): the morphism of topoi
a : Sh((C/K)_total) ⥤ Sh(C/X) is the cocontinuous topos morphism of j_total. -/
@[stacks 0D8C] #check @CategoryTheory.Functor.morphismOfTopoiInOfCocontinuous

/- Remark 85.16.4 (Variant for over an object) (5): the morphisms of topoi
a_n : Sh(C/K_n) ⥤ Sh(C/X) are localizationMorphism (J.over X) K_n. -/
@[stacks 0D8C] #check @CategoryTheory.SemiRepresentableFamily.localizationMorphism

section LowerShriek

open CategoryTheory

universe w u₁ u₂ v₁ v₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [u.IsContinuous J K]

section Sets

variable [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
variable [HasWeakSheafify K (Type w)]
variable (ℱ : Sheaf J (Type w)) (𝒢 : Sheaf K (Type w))

/- Remark 85.16.4 (Variant for over an object) (6): the functor
a_Sh! : Sh((C/K)_total) ⥤ Sh(C/X) is sheafPullback of j_total on Type-valued
sheaves, left adjoint to a⁻¹ via sheafAdjunctionContinuous. -/
@[stacks 0D8C] #check (((u.sheafAdjunctionContinuous (Type w) J K).homEquiv ℱ 𝒢) :
  ((u.sheafPullback (Type w) J K).obj ℱ ⟶ 𝒢) ≃
    (ℱ ⟶ (u.sheafPushforwardContinuous (Type w) J K).obj 𝒢))

end Sets

section Abelian

variable [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasLeftKanExtension P]
variable [HasWeakSheafify K AddCommGrpCat.{w}]
variable (ℱ : Sheaf J AddCommGrpCat.{w}) (𝒢 : Sheaf K AddCommGrpCat.{w})

/- Remark 85.16.4 (Variant for over an object) (7): the functor
a_! : Ab((C/K)_total) ⥤ Ab(C/X) is sheafPullback of j_total on AddCommGrpCat,
left adjoint to a⁻¹ via sheafAdjunctionContinuous, as in Lemma 18.16.2. -/
@[stacks 0D8C] #check (((u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).homEquiv ℱ 𝒢) :
  ((u.sheafPullback AddCommGrpCat.{w} J K).obj ℱ ⟶ 𝒢) ≃
    (ℱ ⟶ (u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj 𝒢))

end Abelian

end LowerShriek
