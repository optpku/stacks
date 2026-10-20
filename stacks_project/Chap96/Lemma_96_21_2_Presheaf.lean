module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import stacks_project.Chap96.«96_5_0_1»
public import stacks_project.Chap96.Lemma_96_17_6_LowerShriek
public import stacks_project.Chap96.Lemma_96_21_2_HigherDirectImage

/-!
# Fibre-product cohomology on associated τ-sites

For a 1-morphism `f : X ⟶ Y` and an object `y` of `Y` lying over a scheme `V`,
the source cohomology assignment is `H^i_τ` of the inverse image of a sheaf along
the projection of the Yoneda 2-fibre product `(Sch/V)_fppf ×_{y, Y} X`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Functor Limits FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)

/-- The fibre object of an object `y` of `Y` over the scheme `Y.p.obj y`. -/
abbrev fiberObj (y : Y.total) : Y.p.Fiber (Y.p.obj y) :=
  ⟨y, rfl⟩

/-- Inverse image of an abelian sheaf along `pr : (Sch/V)_fppf ×_{y, Y} X ⟶ X`. -/
abbrev abelianInverseImage (y : Y.total)
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) :
    Sheaf (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
      AddCommGrpCat.{u + 1} :=
  ((toCartesianBasedFunctor (yonedaFibreProduct.pr f (fiberObj y))).toFunctor.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1}
      (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
      (X.associatedTopology τ)).obj F

/-- `abelianInverseImage f τ y F` is continuous pushforward of `F` along `pr`. -/
theorem abelianInverseImage_eq (y : Y.total)
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) :
    abelianInverseImage f τ y F =
      ((toCartesianBasedFunctor (yonedaFibreProduct.pr f (fiberObj y))).toFunctor.sheafPushforwardContinuous
          AddCommGrpCat.{u + 1}
          (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
          (X.associatedTopology τ)).obj F :=
  rfl

/-- Inverse image of a sheaf of modules along `pr`. -/
abbrev moduleInverseImage (y : Y.total)
    (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) :
    SheafOfModules.{u + 1}
      (associatedStructureSheaf (yonedaFibreProduct f (fiberObj y) : GroupoidsOver S) τ) :=
  (associatedModuleInverseImage (yonedaFibreProduct.pr f (fiberObj y)) τ).obj F

/-- `moduleInverseImage f τ y F` is `associatedModuleInverseImage` along `pr`. -/
theorem moduleInverseImage_eq (y : Y.total)
    (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) :
    moduleInverseImage f τ y F =
      (associatedModuleInverseImage (yonedaFibreProduct.pr f (fiberObj y)) τ).obj F :=
  rfl

/-- Inverse image along `pr` of abelian sheaves is additive. -/
instance abelianInverseImage_additive (y : Y.total) :
    ((toCartesianBasedFunctor (yonedaFibreProduct.pr f (fiberObj y))).toFunctor.sheafPushforwardContinuous
        AddCommGrpCat.{u + 1}
        (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
        (X.associatedTopology τ)).Additive :=
  inferInstance

/-- The projection of a Yoneda 2-fibre product is faithful, as it is representable. -/
instance yonedaFibreProduct.pr_faithful (y : Y.total) :
    Functor.Faithful (toFunctor (yonedaFibreProduct.pr f (fiberObj y))) :=
  sorry

/-- A Yoneda 2-fibre product of categories fibred in groupoids has equalizers. -/
instance yonedaFibreProduct_hasEqualizers (y : Y.total) :
    HasEqualizers (yonedaFibreProduct f (fiberObj y)).total :=
  sorry

/-- Pointwise left Kan extensions along the opposite of `pr` exist on abelian presheaves. -/
instance yonedaFibreProduct.pr_op_hasPointwiseLeftKanExtension_addCommGrpCat (y : Y.total)
    (P : (yonedaFibreProduct f (fiberObj y)).totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (toCartesianBasedFunctor (yonedaFibreProduct.pr f (fiberObj y))).toFunctor.op.HasPointwiseLeftKanExtension
      P :=
  sorry

/-- Inverse image along `pr` preserves injective objects. -/
instance abelianInverseImage_preservesInjectiveObjects (y : Y.total) :
    ((toCartesianBasedFunctor (yonedaFibreProduct.pr f (fiberObj y))).toFunctor.sheafPushforwardContinuous
        AddCommGrpCat.{u + 1}
        (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
        (X.associatedTopology τ)).PreservesInjectiveObjects :=
  sorry

/-- Inverse image along `pr` preserves homology. -/
instance abelianInverseImage_preservesHomology (y : Y.total) :
    ((toCartesianBasedFunctor (yonedaFibreProduct.pr f (fiberObj y))).toFunctor.sheafPushforwardContinuous
        AddCommGrpCat.{u + 1}
        (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
        (X.associatedTopology τ)).PreservesHomology :=
  sorry

/-- Abelian sheaves on a Yoneda 2-fibre product have injective resolutions. -/
instance yonedaFibreProduct_hasInjectiveResolutions (y : Y.total) :
    HasInjectiveResolutions
      (Sheaf (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
        AddCommGrpCat.{u + 1}) :=
  sorry

variable (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (i : ℕ)
variable [∀ y : Y.total,
    HasSheafify (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
      AddCommGrpCat.{u + 1}]
variable [∀ y : Y.total,
    HasExt.{u + 1}
      (Sheaf (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ)
        AddCommGrpCat.{u + 1})]

/-- The cohomology group `H^i_τ((Sch/V)_fppf ×_{y, Y} X, pr⁻¹ F)`. -/
abbrev fibreProductCohomology (y : Y.total) : AddCommGrpCat.{u + 1} :=
  (Sheaf.functorH (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ) i).obj
    (abelianInverseImage f τ y F)

/-- `fibreProductCohomology f τ F i y` is global cohomology of `pr⁻¹ F` on the
Yoneda 2-fibre product. -/
theorem fibreProductCohomology_eq (y : Y.total) :
    fibreProductCohomology f τ F i y =
      (Sheaf.functorH (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ) i).obj
        (abelianInverseImage f τ y F) :=
  rfl

variable (G : SheafOfModules.{u + 1} (associatedStructureSheaf X τ))

/-- The cohomology group `H^i_τ((Sch/V)_fppf ×_{y, Y} X, pr⁻¹ G)` of a sheaf of
modules, computed on the underlying abelian sheaf. -/
abbrev fibreProductModuleCohomology (y : Y.total) : AddCommGrpCat.{u + 1} :=
  (Sheaf.functorH (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ) i).obj
    ((SheafOfModules.toSheaf
        (associatedStructureSheaf (yonedaFibreProduct f (fiberObj y) : GroupoidsOver S) τ)).obj
      (moduleInverseImage f τ y G))

/-- `fibreProductModuleCohomology` is global cohomology of the underlying abelian
sheaf of `pr⁻¹ G`. -/
theorem fibreProductModuleCohomology_eq (y : Y.total) :
    fibreProductModuleCohomology f τ i G y =
      (Sheaf.functorH (associatedTopology (yonedaFibreProduct f (fiberObj y)) τ) i).obj
        ((SheafOfModules.toSheaf
            (associatedStructureSheaf (yonedaFibreProduct f (fiberObj y) : GroupoidsOver S) τ)).obj
          (moduleInverseImage f τ y G)) :=
  rfl

end AlgebraicGeometry.GroupoidsOver
