/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Pseudofunctor
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import stacks_project.Chap96.Lemma_96_17_6_LowerShriek
public import stacks_project.Chap96.Lemma_96_3_3_Pullback
public import stacks_project.Chap96.Lemma_96_5_1_Comparison

/-!
# Associated abelian inverse image and the chosen 2-fibre product

A 1-morphism of categories fibred in groupoids induces abelian inverse image on each associated
`τ`-site as continuous sheaf pushforward of the cartesian total functor. The chosen 2-fibre
product of a cospan `g, f` supplies the 2-cartesian square used for base change, together with
the inverse-image 2-cell `g⁻¹ ∘ (f')⁻¹ ≅ f⁻¹ ∘ (g')⁻¹`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Functor Limits FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The chosen 2-fibre product `Y' ×_Y X` of `g : Y' ⟶ Y` against `f : X ⟶ Y`. -/
abbrev fibreProductApex {X Y Y' : GroupoidsOver S} (f : X ⟶ Y) (g : Y' ⟶ Y) :
    GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f

/-- `fibreProductApex f g` is the explicit 2-fibre-product apex of `g` and `f`. -/
theorem fibreProductApex_eq {X Y Y' : GroupoidsOver S} (f : X ⟶ Y) (g : Y' ⟶ Y) :
    fibreProductApex f g = TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f :=
  rfl

/-- The first projection `f' : Y' ×_Y X ⟶ Y'` of the chosen 2-fibre product. -/
abbrev fibreProductFst {X Y Y' : GroupoidsOver S} (f : X ⟶ Y) (g : Y' ⟶ Y) :
    fibreProductApex f g ⟶ Y' :=
  TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f

/-- `fibreProductFst f g` is the first projection of the 2-fibre product of `g` and `f`. -/
theorem fibreProductFst_eq {X Y Y' : GroupoidsOver S} (f : X ⟶ Y) (g : Y' ⟶ Y) :
    fibreProductFst f g = TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f :=
  rfl

/-- The second projection `g' : Y' ×_Y X ⟶ X` of the chosen 2-fibre product. -/
abbrev fibreProductSnd {X Y Y' : GroupoidsOver S} (f : X ⟶ Y) (g : Y' ⟶ Y) :
    fibreProductApex f g ⟶ X :=
  TwoFibreProduct.snd.{u + 1, u, u + 1, u} g f

/-- `fibreProductSnd f g` is the second projection of the 2-fibre product of `g` and `f`. -/
theorem fibreProductSnd_eq {X Y Y' : GroupoidsOver S} (f : X ⟶ Y) (g : Y' ⟶ Y) :
    fibreProductSnd f g = TwoFibreProduct.snd.{u + 1, u, u + 1, u} g f :=
  rfl

variable {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)

/-- Abelian inverse image `f⁻¹` on associated `τ`-sites, as continuous sheaf pushforward of the
cartesian total functor. -/
abbrev associatedAbelianInverseImage :
    Sheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1} ⥤
      Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1} :=
  (toCartesianBasedFunctor f).toFunctor.sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (X.associatedTopology τ) (Y.associatedTopology τ)

/-- `associatedAbelianInverseImage f τ` is continuous sheaf pushforward of the cartesian total
functor. -/
theorem associatedAbelianInverseImage_eq :
    associatedAbelianInverseImage f τ =
      (toCartesianBasedFunctor f).toFunctor.sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (X.associatedTopology τ) (Y.associatedTopology τ) :=
  rfl

/-- Associated abelian inverse image is additive. -/
instance associatedAbelianInverseImage_additive :
    (associatedAbelianInverseImage f τ).Additive :=
  inferInstance

/-- Associated abelian inverse image preserves homology, recording that a 1-morphism of
algebraic stacks is flat on associated `τ`-sites. -/
instance associatedAbelianInverseImage_preservesHomology :
    (associatedAbelianInverseImage f τ).PreservesHomology :=
  sorry

/-- Associated abelian inverse image preserves finite limits. -/
instance associatedAbelianInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (associatedAbelianInverseImage f τ) :=
  sorry

/-- Associated abelian inverse image preserves finite colimits. -/
instance associatedAbelianInverseImage_preservesFiniteColimits :
    PreservesFiniteColimits (associatedAbelianInverseImage f τ) :=
  sorry

variable {Z : GroupoidsOver S} (h : Y ⟶ Z)

/-- Inverse image along a composite 1-morphism identifies with the composite of inverse
images. -/
def associatedAbelianInverseImage_compIso :
    associatedAbelianInverseImage (f ≫ h) τ ≅
      associatedAbelianInverseImage h τ ⋙ associatedAbelianInverseImage f τ :=
  (sheafPushforwardContinuousComp'
      (ObjectProperty.FullSubbicategory.toFunctor.compIso f h)
      AddCommGrpCat.{u + 1}
      (X.associatedTopology τ) (Y.associatedTopology τ) (Z.associatedTopology τ)).symm

/-- `associatedAbelianInverseImage_compIso` is the continuous-pushforward comparison along
total-functor composition. -/
theorem associatedAbelianInverseImage_compIso_eq :
    associatedAbelianInverseImage_compIso f τ h =
      (sheafPushforwardContinuousComp'
          (ObjectProperty.FullSubbicategory.toFunctor.compIso f h)
          AddCommGrpCat.{u + 1}
          (X.associatedTopology τ) (Y.associatedTopology τ) (Z.associatedTopology τ)).symm :=
  rfl

variable {Y' : GroupoidsOver S} (g : Y' ⟶ Y)

/-- The inverse-image 2-cell of the chosen 2-fibre product:
`g⁻¹ ∘ (f')⁻¹ ≅ f⁻¹ ∘ (g')⁻¹`. -/
def abelianInverseImage_twoFibreIso :
    associatedAbelianInverseImage g τ ⋙ associatedAbelianInverseImage (fibreProductFst f g) τ ≅
      associatedAbelianInverseImage f τ ⋙ associatedAbelianInverseImage (fibreProductSnd f g) τ :=
  (associatedAbelianInverseImage_compIso (fibreProductFst f g) τ g).symm ≪≫
    sheafPushforwardContinuousIso
        (toFunctorIso (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} g f))
        AddCommGrpCat.{u + 1}
        ((fibreProductApex f g).associatedTopology τ) (Y.associatedTopology τ) ≪≫
      associatedAbelianInverseImage_compIso (fibreProductSnd f g) τ f

/-- `abelianInverseImage_twoFibreIso` is the composite of composition comparisons with the
2-fibre-product 2-cell. -/
theorem abelianInverseImage_twoFibreIso_eq :
    abelianInverseImage_twoFibreIso f τ g =
      (associatedAbelianInverseImage_compIso (fibreProductFst f g) τ g).symm ≪≫
        sheafPushforwardContinuousIso
            (toFunctorIso (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} g f))
            AddCommGrpCat.{u + 1}
            ((fibreProductApex f g).associatedTopology τ) (Y.associatedTopology τ) ≪≫
          associatedAbelianInverseImage_compIso (fibreProductSnd f g) τ f :=
  rfl

end AlgebraicGeometry.GroupoidsOver
