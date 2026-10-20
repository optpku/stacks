module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap96.Lemma_96_21_2_HigherDirectImage
public import stacks_project.Chap96.Lemma_96_21_2_Presheaf
public import stacks_project.Chap96.Lemma_96_21_2_Comparison

/-!
# Lemma 96.21.2

For a 1-morphism of algebraic stacks, the higher direct image `R^i f_* F` on an
associated `τ`-site is the sheaf associated to the presheaf sending an object
`y` of `Y` over a scheme `V` to `H^i_τ` of `pr⁻¹ F` on the Yoneda 2-fibre product
`(Sch/V)_fppf ×_{y, Y} X`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable (f : X ⟶ Y) (τ : StandardTopology)
variable [HasSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}]
variable [HasSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}]
variable [HasInjectiveResolutions
    (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})]
variable [∀ y : Y.total,
    HasSheafify (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
      AddCommGrpCat.{u + 1}]
variable [∀ y : Y.total,
    HasExt.{u + 1}
      (Sheaf (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
        AddCommGrpCat.{u + 1})]

/-- Lemma 96.21.2 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a 1-morphism of
algebraic stacks over `S`. Let `τ` be one of Zariski, étale, smooth, syntomic, or
fppf. Let `F` be an object of `Ab(X_τ)`. Then the sheaf `R^i f_* F` is the sheaf
associated to the presheaf sending an object `y` of `Y` lying over a scheme `V` to
`H^i_τ((Sch/V)_fppf ×_{y, Y} X, pr⁻¹ F)`. -/
@[stacks 075G]
def sheafify_higherDirectImagePresheaf_iso
    [AlgebraicStack X] [AlgebraicStack Y]
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (i : ℕ) :
    sheafify_higherDirectImagePresheaf f τ F i ≅ higherDirectImage f τ F i :=
  sheafify_higherDirectImagePresheafIso_composite f τ F i

/-- The labeled abelian identification equals the injective-resolution composite
with the homology-to-fibre-product-cohomology comparison. -/
theorem sheafify_higherDirectImagePresheaf_iso_spec
    [AlgebraicStack X] [AlgebraicStack Y]
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (i : ℕ) :
    sheafify_higherDirectImagePresheaf_iso f τ F i =
      sheafify_higherDirectImagePresheafIso_composite f τ F i :=
  sorry

variable (G : SheafOfModules.{u + 1} (associatedStructureSheaf X τ))
variable [HasWeakSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}]
variable [∀ y : Y.total,
    ∀ P : (yonedaFibreProduct f (fiberObj y)).totalᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (toCartesianBasedFunctor (yonedaFibreProduct.pr f (fiberObj y))).toFunctor.op.HasLeftKanExtension
        P]

/-- Lemma 96.21.2 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a 1-morphism of
algebraic stacks over `S`. Let `τ` be one of Zariski, étale, smooth, syntomic, or
fppf. Let `G` be an object of `Mod(X_τ, O_X)`. Then the sheaf `R^i f_* G` is the
sheaf associated to the presheaf sending an object `y` of `Y` lying over a scheme
`V` to `H^i_τ((Sch/V)_fppf ×_{y, Y} X, pr⁻¹ G)`. -/
@[stacks 075G]
def sheafify_higherDirectImageModulePresheaf_iso
    [AlgebraicStack X] [AlgebraicStack Y] (i : ℕ) :
    sheafify_higherDirectImageModulePresheaf f τ G i ≅
      (SheafOfModules.toSheaf (associatedStructureSheaf Y τ)).obj
        (higherDirectImageModule f τ G i) :=
  sheafify_higherDirectImageModulePresheafIso_composite f τ G i

/-- The labeled module identification equals the named injective-resolution
composite comparing fibre-product cohomology of `pr⁻¹ G` with the underlying
abelian sheaf of the module-valued `R^i f_* G`. -/
theorem sheafify_higherDirectImageModulePresheaf_iso_spec
    [AlgebraicStack X] [AlgebraicStack Y] (i : ℕ) :
    sheafify_higherDirectImageModulePresheaf_iso f τ G i =
      sheafify_higherDirectImageModulePresheafIso_composite f τ G i :=
  sorry

end AlgebraicGeometry.GroupoidsOver
