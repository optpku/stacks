/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Limits.Final.Type
public import ReasLib.CategoryTheory.Fibered.Groupoids.Cech.Simplex

/-!
# The Čech complex of a 1-morphism of categories fibred in groupoids

Global sections of an abelian presheaf on a total category, the associated
cosimplicial abelian group of a covering simplex, and the Čech cochain complex.
-/

@[expose] public section

open CategoryTheory AlgebraicTopology
open scoped Bicategory Simplicial

noncomputable section

universe u v w vS wA uD vD

namespace CategoryTheory.FiberedCategoryOver.Groupoids.Cech

variable {C : Type u} [Category.{v} C]
variable {U X : FiberedCategoryOver.Groupoids C}

/-- Pointwise additive commutative group structure on sections of an abelian-group-valued
functor. -/
instance sectionsAddCommGroup {J : Type uD} [Category.{vD} J]
    (G : J ⥤ AddCommGrpCat.{wA}) :
    AddCommGroup (G ⋙ forget AddCommGrpCat.{wA}).sections :=
  AddSubgroup.toAddCommGroup (G := ∀ j, G.obj j)
    (AddGrpCat.sectionsAddSubgroup (G ⋙ forget₂ AddCommGrpCat AddGrpCat))

/-- Global sections `Γ(D, G)` of an abelian presheaf on a category `D`. -/
def globalSections {D : Type uD} [Category.{vD} D]
    (G : Dᵒᵖ ⥤ AddCommGrpCat.{wA}) : AddCommGrpCat.{max uD wA} :=
  AddCommGrpCat.of (G ⋙ forget AddCommGrpCat.{wA}).sections

/-- The carrier of `globalSections G` is the type of sections of `G ⋙ forget`. -/
theorem globalSections_carrier {D : Type uD} [Category.{vD} D]
    (G : Dᵒᵖ ⥤ AddCommGrpCat.{wA}) :
    globalSections G = AddCommGrpCat.of (G ⋙ forget AddCommGrpCat.{wA}).sections :=
  rfl

/-- Pullback of global sections along a functor of total categories. -/
def globalSectionsMap {D E : Type uD} [Category.{vD} D] [Category.{vD} E]
    (u : D ⥤ E) (G : Eᵒᵖ ⥤ AddCommGrpCat.{wA}) :
    globalSections G ⟶ globalSections (u.op ⋙ G) := by
  refine AddCommGrpCat.ofHom
    { toFun := fun s ↦ u.op.sectionsPrecomp (P := G ⋙ forget AddCommGrpCat.{wA}) s
      map_zero' := ?_
      map_add' := ?_ }
  all_goals sorry

/-- The `n`-th Čech term is global sections of `f_n⁻¹ F` on `U_n`. -/
def term (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) (n : SimplexCategory) :=
  globalSections ((apexFunctor f n).op ⋙ F)

/-- The cosimplicial abelian group `n ↦ Γ(U_n, f_n⁻¹ F)`. -/
def cosimplicial (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) :
    CosimplicialObject AddCommGrpCat := by
  refine {
    obj n := term f F n
    map {m n} φ := globalSectionsMap (reindex φ) ((apexFunctor f m).op ⋙ F)
    map_id := ?_
    map_comp := ?_
  }
  all_goals sorry

/-- The Čech complex `Cech^•(U ⟶ X, F)` associated to a 1-morphism of categories
fibred in groupoids and an abelian presheaf on `X`. -/
def complex (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) :
    CochainComplex AddCommGrpCat ℕ :=
  (alternatingCofaceMapComplex _).obj (cosimplicial f F)

/-- Degree `n` of the Čech complex is `Γ(U_n, f_n⁻¹ F)`. -/
theorem complex_X (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) (n : ℕ) :
    (complex f F).X n = globalSections ((apexFunctor f ⦋n⦌).op ⋙ F) := sorry

/-- The Čech differential is the alternating sum of coface maps. -/
theorem complex_d (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) (n : ℕ) :
    (complex f F).d n (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (cosimplicial f F).δ i := sorry

end CategoryTheory.FiberedCategoryOver.Groupoids.Cech
