/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.Homology.Augment
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import ReasLib.Algebra.Homology.Homotopy.Contractible
public import ReasLib.CategoryTheory.Fibered.Groupoids.Cech.Complex
public import ReasLib.CategoryTheory.Fibered.Groupoids.UnderlyingFunctorIso

/-!
# The extended Čech complex of a morphism of categories fibred in groupoids

The canonical coaugmentation of the Čech complex places global sections of the
target in degree zero. A section up to two-isomorphism induces an extra
degeneracy on covering simplices and makes the extended complex contractible.
-/

@[expose] public section

open CategoryTheory AlgebraicTopology
open scoped Bicategory Simplicial

noncomputable section

universe u v w vS wA

namespace CategoryTheory.FiberedCategoryOver.Groupoids.Cech

section ExtraSimplex

variable {C : Type u} [Category.{v} C]
variable {U X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}

/-- The vertices obtained by appending the image under a section of the apex
to the original vertices of a covering simplex. -/
def extraSimplexVertices {f : U ⟶ X} (s : X ⟶ U) {n : SimplexCategory}
    (P : Simplex.Obj f n) : Fin (n.len + 2) → U.total :=
  Fin.snoc P.vertices ((toFunctor s).obj P.apex)

/-- Appending a vertex preserves the original vertices on `Fin.castSucc`. -/
theorem extraSimplexVertices_castSucc {f : U ⟶ X} (s : X ⟶ U)
    {n : SimplexCategory} (P : Simplex.Obj f n) (i : Fin (n.len + 1)) :
    extraSimplexVertices s P i.castSucc = P.vertices i :=
  Fin.snoc_castSucc _ _ _

/-- The appended vertex is the image of the apex under the section. -/
theorem extraSimplexVertices_last {f : U ⟶ X} (s : X ⟶ U)
    {n : SimplexCategory} (P : Simplex.Obj f n) :
    extraSimplexVertices s P (Fin.last (n.len + 1)) = (toFunctor s).obj P.apex :=
  Fin.snoc_last _ _

/-- The extra degeneracy on covering simplices appends the image of the apex
under a section, with structure isomorphism given by the section two-isomorphism.
On morphisms it appends the image of the apex map under the section. -/
def extraSimplexFunctor {f : U ⟶ X} (s : X ⟶ U) (t : s ≫ f ≅ 𝟙 X)
    (n : SimplexCategory) :
    Simplex.Obj f n ⥤ Simplex.Obj f (SimplexCategory.mk (n.len + 1)) where
  obj P := Simplex.objMk (extraSimplexVertices s P) P.apex (fun i ↦
    Fin.lastCases
      (eqToIso (congrArg (fun u ↦ (toFunctor f).obj u) (extraSimplexVertices_last s P)) ≪≫
        eqToIso (Functor.congr_obj (toFunctor.comp s f).symm P.apex) ≪≫
        (toFunctorIso t).app P.apex ≪≫
        eqToIso (Functor.congr_obj (toFunctor.id X) P.apex))
      (fun j ↦
        eqToIso (congrArg (fun u ↦ (toFunctor f).obj u)
            (extraSimplexVertices_castSucc s P j)) ≪≫
          P.iso j)
      i)
  map {P Q} ψ := Simplex.homMk (fun i ↦
    Fin.lastCases
      (eqToHom (extraSimplexVertices_last s P) ≫
        (toFunctor s).map ψ.apex ≫
        eqToHom (extraSimplexVertices_last s Q).symm)
      (fun j ↦
        eqToHom (extraSimplexVertices_castSucc s P j) ≫
          ψ.vertex j ≫
          eqToHom (extraSimplexVertices_castSucc s Q j).symm)
      i) ψ.apex sorry
  map_id := sorry
  map_comp := sorry

end ExtraSimplex

section Extended

variable {C : Type u} [Category.{v} C]
variable {U X : FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C}

/-- The Čech coaugmentation pulls global sections back along the degree-zero
apex functor. -/
def coaugmentation (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) :
    globalSections F ⟶ (complex f F).X 0 :=
  globalSectionsMap (apexFunctor f ⦋0⦌) F ≫ eqToHom (complex_X f F 0).symm

/-- The Čech coaugmentation equalizes every pair of maps out of `⦋0⦌`. -/
theorem coaugmentation_comp_map (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA})
    (i : SimplexCategory) (g₁ g₂ : ⦋0⦌ ⟶ i) :
    coaugmentation f F ≫ eqToHom (complex_X f F 0) ≫ (cosimplicial f F).map g₁ =
      coaugmentation f F ≫ eqToHom (complex_X f F 0) ≫ (cosimplicial f F).map g₂ :=
  sorry

/-- The augmented Čech cosimplicial abelian group has augmentation object
the global sections of the presheaf on the target. -/
def augmented (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) :
    CosimplicialObject.Augmented AddCommGrpCat :=
  (cosimplicial f F).augment (globalSections F)
    (coaugmentation f F ≫ eqToHom (complex_X f F 0))
    (coaugmentation_comp_map f F)

/-- The coaugmentation is a cocycle in degree zero of the Čech complex. -/
theorem coaugmentation_comp_d (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) :
    coaugmentation f F ≫ (complex f F).d 0 1 = 0 :=
  sorry

/-- The extended Čech cochain complex places global sections of the target in
degree zero and shifts the ordinary Čech complex to positive degrees. -/
def extended (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) :
    CochainComplex AddCommGrpCat ℕ :=
  CochainComplex.augment (complex f F) (coaugmentation f F) (coaugmentation_comp_d f F)

/-- Degree zero of the extended Čech complex is the global sections of the
presheaf on the target. -/
theorem extended_X_zero (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) :
    (extended f F).X 0 = globalSections F :=
  rfl

/-- Positive degrees of the extended Čech complex recover the ordinary Čech
complex. -/
theorem extended_X_succ (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) (n : ℕ) :
    (extended f F).X (n + 1) = (complex f F).X n :=
  rfl

/-- The first differential of the extended Čech complex is the coaugmentation. -/
theorem extended_d_zero_one (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) :
    (extended f F).d 0 1 = coaugmentation f F :=
  rfl

/-- The extended Čech complex of an abelian presheaf is contractible whenever
the morphism of categories fibred in groupoids admits a section up to two-isomorphism. -/
theorem extended_contractible_of_section (f : U ⟶ X) (s : X ⟶ U) (t : s ≫ f ≅ 𝟙 X)
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) :
    (extended f F).Contractible :=
  sorry

end Extended

end CategoryTheory.FiberedCategoryOver.Groupoids.Cech
