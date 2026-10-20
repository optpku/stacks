/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Family.Simplicial.HomComplex
public import ReasLib.CategoryTheory.Sites.Family.Simplicial.Cech

/-!
# Canonical comparison of internal-Hom and Čech complexes
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open CategoryTheory.GrothendieckTopology.SemiRepresentableLocalization
open FormalCoproduct
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (K : SimplicialObject (FormalCoproduct.{w} C))
variable [HasWeakSheafify J AddCommGrpCat.{max w u v}]
variable [∀ n : SimplexCategory,
    ∀ P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
      (forget (K.obj (op n))).op.HasPointwiseRightKanExtension P]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ∀ P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
      (overMap (K.map φ.op)).op.HasPointwiseRightKanExtension P]

set_option backward.privateInPublic true in
/-- The sheafification unit of the free abelian presheaf on `F(K_n)`, evaluated at `V`. -/
private def homToCech_toSheafify (n : ℕ) (V : Cᵒᵖ) :
    (FreeAbelianPresheaf.obj ((simplicialPresheafULift K).obj (op ⦋n⦌))).obj V ⟶
      ((freeAbelianComplex J K).X n).obj.obj V :=
  ((sheafificationAdjunction J AddCommGrpCat.{max w u v}).unit.app
      (FreeAbelianPresheaf.obj ((simplicialPresheafULift K).obj (op ⦋n⦌)))).app V

set_option backward.privateInPublic true in
/-- Canonical generator of `F(K_n)` at the source of a localization object `U`. -/
private def homToCech_generator (n : ℕ) (U : OverSite (K.obj (op ⦋n⦌))) :
    ((simplicialPresheafULift K).obj (op ⦋n⦌)).obj
      (op ((forget (K.obj (op ⦋n⦌))).obj U)) :=
  ULift.up
    (toPresheafObjMk (K.obj (op ⦋n⦌))
      (op ((forget (K.obj (op ⦋n⦌))).obj U)) U.1 U.2.hom)

set_option backward.privateInPublic true in
/-- Image of `homToCech_generator` in the free abelian sheaf `Z_{F(K_n)}`. -/
private def homToCech_generatorFree (n : ℕ) (U : OverSite (K.obj (op ⦋n⦌))) :
    (CategoryTheory.forget AddCommGrpCat.{max w u v}).obj
      (((freeAbelianComplex J K).X n).obj.obj
        (op ((forget (K.obj (op ⦋n⦌))).obj U))) :=
  (CategoryTheory.forget AddCommGrpCat.{max w u v}).map
      (homToCech_toSheafify J K n
        (op ((forget (K.obj (op ⦋n⦌))).obj U)))
    (FreeAbelianGroup.of (homToCech_generator K n U))

/-- Evaluation at the canonical free generator preserves zero. -/
private theorem homToCech_evalApp_map_zero (F : Sheaf J AddCommGrpCat.{max w u v})
    (n : ℕ) (U : (OverSite (K.obj (op ⦋n⦌)))ᵒᵖ) :
    (fun α : ((abelianStageInverseImage J K ⦋n⦌).obj ((homComplex J K F).X n)).obj.obj U ↦
        (CategoryTheory.forget AddCommGrpCat.{max w u v}).map
            (α.app (op (CategoryTheory.Over.mk
              (CategoryTheory.CategoryStruct.id
                ((forget (K.obj (op ⦋n⦌))).obj U.unop)))))
          (homToCech_generatorFree J K n U.unop)) (0 : ((abelianStageInverseImage J K ⦋n⦌).obj ((homComplex J K F).X n)).obj.obj U) = 0 :=
  sorry

/-- Evaluation at the canonical free generator preserves addition. -/
private theorem homToCech_evalApp_map_add (F : Sheaf J AddCommGrpCat.{max w u v})
    (n : ℕ) (U : (OverSite (K.obj (op ⦋n⦌)))ᵒᵖ)
    (α β : ((abelianStageInverseImage J K ⦋n⦌).obj ((homComplex J K F).X n)).obj.obj U) :
    (fun α : ((abelianStageInverseImage J K ⦋n⦌).obj ((homComplex J K F).X n)).obj.obj U ↦
        (CategoryTheory.forget AddCommGrpCat.{max w u v}).map
            (α.app (op (CategoryTheory.Over.mk
              (CategoryTheory.CategoryStruct.id
                ((forget (K.obj (op ⦋n⦌))).obj U.unop)))))
          (homToCech_generatorFree J K n U.unop)) (α + β) =
      (fun α : ((abelianStageInverseImage J K ⦋n⦌).obj ((homComplex J K F).X n)).obj.obj U ↦
        (CategoryTheory.forget AddCommGrpCat.{max w u v}).map
            (α.app (op (CategoryTheory.Over.mk
              (CategoryTheory.CategoryStruct.id
                ((forget (K.obj (op ⦋n⦌))).obj U.unop)))))
          (homToCech_generatorFree J K n U.unop)) α +
        (fun α : ((abelianStageInverseImage J K ⦋n⦌).obj ((homComplex J K F).X n)).obj.obj U ↦
        (CategoryTheory.forget AddCommGrpCat.{max w u v}).map
            (α.app (op (CategoryTheory.Over.mk
              (CategoryTheory.CategoryStruct.id
                ((forget (K.obj (op ⦋n⦌))).obj U.unop)))))
          (homToCech_generatorFree J K n U.unop)) β :=
  sorry

set_option backward.privateInPublic true in
/-- Evaluation of a local Hom at the canonical generator of `K_n` at `U`. -/
private def homToCech_evalApp (F : Sheaf J AddCommGrpCat.{max w u v}) (n : ℕ)
    (U : (OverSite (K.obj (op ⦋n⦌)))ᵒᵖ) :
    ((abelianStageInverseImage J K ⦋n⦌).obj ((homComplex J K F).X n)).obj.obj U ⟶
      ((abelianStageInverseImage J K ⦋n⦌).obj F).obj.obj U :=
  AddCommGrpCat.ofHom
    { toFun := fun α ↦
        (CategoryTheory.forget AddCommGrpCat.{max w u v}).map
            (α.app (op (CategoryTheory.Over.mk
              (CategoryTheory.CategoryStruct.id
                ((forget (K.obj (op ⦋n⦌))).obj U.unop)))))
          (homToCech_generatorFree J K n U.unop)
      map_zero' := homToCech_evalApp_map_zero J K F n U
      map_add' := homToCech_evalApp_map_add J K F n U }

/-- Naturality of generator evaluation in the localization site. -/
private theorem homToCech_evalApp_naturality (F : Sheaf J AddCommGrpCat.{max w u v}) (n : ℕ)
    {U U' : (OverSite (K.obj (op ⦋n⦌)))ᵒᵖ} (f : U ⟶ U') :
    ((abelianStageInverseImage J K ⦋n⦌).obj ((homComplex J K F).X n)).obj.map f ≫
        homToCech_evalApp J K F n U' =
      homToCech_evalApp J K F n U ≫
        ((abelianStageInverseImage J K ⦋n⦌).obj F).obj.map f :=
  sorry

set_option backward.privateInPublic true in
/-- Inverse image of `Hom(Z_{F(K_n)}, F)` evaluates onto inverse image of `F`. -/
private def homToCech_eval (F : Sheaf J AddCommGrpCat.{max w u v}) (n : ℕ) :
    (abelianStageInverseImage J K ⦋n⦌).obj ((homComplex J K F).X n) ⟶
      (abelianStageInverseImage J K ⦋n⦌).obj F where
  hom :=
    { app := fun U ↦ homToCech_evalApp J K F n U
      naturality := fun _ _ f ↦ homToCech_evalApp_naturality J K F n f }

set_option backward.privateInPublic true in
/-- Degreewise comparison `Hom(Z_{F(K_n)}, F) ⟶ j_{n,*} j_n⁻¹ F` as the adjunct of
generator evaluation. -/
def homToCech_f (F : Sheaf J AddCommGrpCat.{max w u v}) (n : ℕ) :
    (homComplex J K F).X n ⟶ (cechComplex J K F).X n :=
  by
    exact (@Functor.sheafAdjunctionCocontinuous _ _ _ _ (forget (K.obj (op ⦋n⦌)))
        AddCommGrpCat.{max w u v} _
        (overTopology J (K.obj (op ⦋n⦌))) J _ _
        (forget_isContinuous J (K.obj (op ⦋n⦌)))).homEquiv
      ((homComplex J K F).X n)
      ((abelianStageInverseImage J K ⦋n⦌).obj F)
      (homToCech_eval J K F n)

/-- Differentials intertwine the degreewise Hom-to-Čech comparison. -/
private theorem homToCech_comm (F : Sheaf J AddCommGrpCat.{max w u v}) (i j : ℕ)
    (hij : (ComplexShape.up ℕ).Rel i j) :
    homToCech_f J K F i ≫ (cechComplex J K F).d i j =
      (homComplex J K F).d i j ≫ homToCech_f J K F j :=
  sorry

/-- The canonical comparison morphism identifying `Hom(s(Z_{F(K)^#}), F)` with the
unaugmented Čech cochain of `a⁻¹ F`. -/
def homToCech (F : Sheaf J AddCommGrpCat.{max w u v}) :
    homComplex J K F ⟶ cechComplex J K F where
  f n := homToCech_f J K F n
  comm' i j hij := by exact homToCech_comm J K F i j hij

/-- The canonical generator-evaluation comparison from the internal-Hom complex of
free abelian sheaves to the push-pull Čech complex is an isomorphism. -/
instance homToCech_isIso (J : GrothendieckTopology C)
    [HasEqualizers C] [HasPullbacks C]
    (K : SimplicialObject (FormalCoproduct.{w} C))
    [HasWeakSheafify J AddCommGrpCat.{max w u v}]
    [∀ n : SimplexCategory,
      ∀ P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
        (forget (K.obj (op n))).op.HasPointwiseRightKanExtension P]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n),
      ∀ P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
        (overMap (K.map φ.op)).op.HasPointwiseRightKanExtension P]
    (F : Sheaf J AddCommGrpCat.{max w u v}) :
    IsIso (homToCech J K F) :=
  sorry

end CategoryTheory.SemiRepresentableFamily
