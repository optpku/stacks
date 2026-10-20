/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Hom
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Presheaf
public import ReasLib.CategoryTheory.Sites.Sheafification.FreeAbelian

/-!
# Free abelian and internal-Hom complexes of simplicial families
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (K : SimplicialObject (FormalCoproduct.{w} C))
variable [HasWeakSheafify J AddCommGrpCat.{max w u v}]

/-- Universe-aligned simplicial presheaf `F(K)` of a simplicial family. -/
def simplicialPresheafULift :
    SimplicialObject (Cᵒᵖ ⥤ Type (max w u v)) :=
  K ⋙ FormalCoproduct.toPresheaf ⋙
    (Functor.whiskeringRight Cᵒᵖ (Type (max w v)) (Type (max w u v))).obj
      CategoryTheory.uliftFunctor.{u, max w v}

/-- The simplicial abelian sheaf obtained by freely abelianizing `F(K)` degreewise. -/
def freeAbelianSimplicial :
    SimplicialObject (Sheaf J AddCommGrpCat.{max w u v}) :=
  simplicialPresheafULift K ⋙ J.freeAbelianSheafFunctor

/-- The alternating-face chain complex of the degreewise free abelian sheaves. -/
def freeAbelianComplex :
    ChainComplex (Sheaf J AddCommGrpCat.{max w u v}) ℕ :=
  (alternatingFaceMapComplex (Sheaf J AddCommGrpCat.{max w u v})).obj
    (freeAbelianSimplicial J K)

/-- Degree `n` of `freeAbelianComplex` is the free abelian sheaf on the universe-lift of
`F(K_n)`. -/
theorem freeAbelianComplex_X (n : ℕ) :
    (freeAbelianComplex J K).X n =
      J.freeAbelianSheaf ((simplicialPresheafULift K).obj (op ⦋n⦌)) :=
  rfl

/-- The internal-Hom differential vanishes outside adjacent degrees. -/
private theorem homComplex_shape (F : Sheaf J AddCommGrpCat.{max w u v}) (i j : ℕ)
    (hij : ¬ (ComplexShape.up ℕ).Rel i j) :
    abelianSheafHom_map J ((freeAbelianComplex J K).X i) ((freeAbelianComplex J K).X j) F
        ((freeAbelianComplex J K).d j i) = 0 :=
  sorry

/-- Consecutive differentials of the Hom cochain compose to zero. -/
private theorem homComplex_d_comp_d (F : Sheaf J AddCommGrpCat.{max w u v}) (i j k : ℕ) :
    abelianSheafHom_map J ((freeAbelianComplex J K).X i) ((freeAbelianComplex J K).X j) F
          ((freeAbelianComplex J K).d j i) ≫
        abelianSheafHom_map J ((freeAbelianComplex J K).X j) ((freeAbelianComplex J K).X k) F
          ((freeAbelianComplex J K).d k j) = 0 :=
  sorry

/-- The cochain complex `Hom(s(Z_{F(K)^#}), F)` of abelian sheaves. -/
def homComplex (F : Sheaf J AddCommGrpCat.{max w u v}) :
    CochainComplex (Sheaf J AddCommGrpCat.{max w u v}) ℕ where
  X n := abelianSheafHom J ((freeAbelianComplex J K).X n) F
  d i j :=
    abelianSheafHom_map J ((freeAbelianComplex J K).X i) ((freeAbelianComplex J K).X j) F
      ((freeAbelianComplex J K).d j i)
  shape i j hij := by exact homComplex_shape J K F i j hij
  d_comp_d' i j k _ _ := by exact homComplex_d_comp_d J K F i j k

/-- Degree `n` of `homComplex` is `abelianSheafHom` of the degree-`n` free abelian sheaf
into `F`. -/
theorem homComplex_X (F : Sheaf J AddCommGrpCat.{max w u v}) (n : ℕ) :
    (homComplex J K F).X n = abelianSheafHom J ((freeAbelianComplex J K).X n) F :=
  rfl

end CategoryTheory.SemiRepresentableFamily
