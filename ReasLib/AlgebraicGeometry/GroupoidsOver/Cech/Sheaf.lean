module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Augment
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Topology
public import ReasLib.CategoryTheory.Fibered.Groupoids.RelativeCech.Extended

/-!
# The extended relative Čech complex of an abelian sheaf

Sheafification of `RelativeCech.complex` on the associated `τ`-site, the
coaugmentation `F ⟶ f_{0,*} f_0⁻¹ F` in `Ab(𝒳_τ)`, and the ℕ-indexed
extended complex with `F` in degree 0.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver AlgebraicTopology CategoryTheory Functor
open scoped Bicategory Simplicial

noncomputable section

universe u

namespace CategoryTheory.FiberedCategoryOver.Groupoids.RelativeCech

open Cech

variable {S : Scheme.{u}} {U X : GroupoidsOver S}

/-- The sheafified relative Čech complex of a 1-morphism of categories fibred
in groupoids and an abelian sheaf on the associated `τ`-site. -/
def complexSheaf (f : U ⟶ X) (τ : StandardTopology)
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})
    [HasWeakSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}] :
    CochainComplex (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) ℕ :=
  ((presheafToSheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (complex f F.obj)

/-- Degree `n` of `complexSheaf` is the sheafification of `f_{n,*} f_n⁻¹ F`. -/
theorem complexSheaf_X (f : U ⟶ X) (τ : StandardTopology)
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})
    [HasWeakSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}] (n : ℕ) :
    (complexSheaf f τ F).X n =
      (presheafToSheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}).obj
        ((complex f F.obj).X n) :=
  rfl

/-- The coaugmentation `F ⟶ f_{0,*} f_0⁻¹ F` in `Ab(𝒳_τ)`, obtained by mapping
the presheaf-level relative Čech coaugmentation along sheafification. -/
def coaugmentationSheaf (f : U ⟶ X) (τ : StandardTopology)
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})
    [HasWeakSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}] :
    F ⟶ (complexSheaf f τ F).X 0 :=
  (sheafificationIso F).hom ≫
    (presheafToSheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}).map
      (coaugmentation f F.obj)

/-- The sheaf-level relative Čech coaugmentation is a cocycle in degree 0. -/
theorem coaugmentationSheaf_comp_d (f : U ⟶ X) (τ : StandardTopology)
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})
    [HasWeakSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}] :
    coaugmentationSheaf f τ F ≫ (complexSheaf f τ F).d 0 1 = 0 :=
  sorry

/-- The extended relative Čech cochain complex of an abelian sheaf on `𝒳_τ`,
obtained by placing `F` in degree 0. -/
def extendedSheaf (f : U ⟶ X) (τ : StandardTopology)
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})
    [HasWeakSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}] :
    CochainComplex (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) ℕ :=
  CochainComplex.augment (complexSheaf f τ F) (coaugmentationSheaf f τ F)
    (coaugmentationSheaf_comp_d f τ F)

/-- Degree 0 of the extended sheaf-level relative Čech complex is `F`, the
source term in degree -1. -/
theorem extendedSheaf_X_zero (f : U ⟶ X) (τ : StandardTopology)
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})
    [HasWeakSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}] :
    (extendedSheaf f τ F).X 0 = F :=
  rfl

/-- Positive degrees of the extended sheaf-level relative Čech complex recover
the sheafified relative Čech complex. -/
theorem extendedSheaf_X_succ (f : U ⟶ X) (τ : StandardTopology)
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})
    [HasWeakSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}] (n : ℕ) :
    (extendedSheaf f τ F).X (n + 1) = (complexSheaf f τ F).X n :=
  rfl

/-- The first differential of the extended sheaf-level relative Čech complex is
the sheaf coaugmentation. -/
theorem extendedSheaf_d_zero_one (f : U ⟶ X) (τ : StandardTopology)
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})
    [HasWeakSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}] :
    (extendedSheaf f τ F).d 0 1 = coaugmentationSheaf f τ F :=
  rfl

end CategoryTheory.FiberedCategoryOver.Groupoids.RelativeCech
