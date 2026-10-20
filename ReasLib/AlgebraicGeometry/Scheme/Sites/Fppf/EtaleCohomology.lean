module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Small
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Situation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Abelian coefficients for the fppf–étale cohomology comparison

The essential image of the small-to-big étale inverse image gives the coefficient
families for comparing fppf and étale cohomology along finite morphisms.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale.SmallToBig
open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.GrothendieckTopology
open CategoryTheory.MorphismProperty

noncomputable section

universe u i

namespace AlgebraicGeometry.Scheme.FppfEtale

section Coefficients

variable (X : Scheme.{u})

/-- Inverse image `π_X⁻¹` on abelian sheaves along identity-base étale relocalization, with
abelian groups in universe `u + 1`. -/
abbrev piInverseImage :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1} :=
  (relocalizationFunctor (𝟙 X)).sheafPullback AddCommGrpCat.{u + 1}
    X.smallEtaleTopology (etaleTopology.over X)

/-- Direct image `π_{X,*}` on abelian sheaves along identity-base étale relocalization. -/
abbrev piPushforward :
    Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (relocalizationFunctor (𝟙 X)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    X.smallEtaleTopology (etaleTopology.over X)

/-- Sheaf-level adjunction `π_X⁻¹ ⊣ π_{X,*}`. -/
def piAdjunction : piInverseImage X ⊣ piPushforward X :=
  (relocalizationFunctor (𝟙 X)).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    X.smallEtaleTopology (etaleTopology.over X)

/-- The isomorphism-closed essential image of the small-to-big étale inverse image on abelian sheaves. -/
@[stacks 0F0H "essential image of the small-to-big étale inverse image"]
abbrev essImageAb :
    ObjectProperty (Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1}) :=
  Functor.essImage (piInverseImage X)

/-- The essential-image coefficient family is a weak Serre class. -/
@[stacks 0F0H "weak Serre essential image"]
instance essImageAb_isWeakSerre
    [Abelian (Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1})] :
    IsWeakSerreClass (essImageAb X) := sorry

end Coefficients

/-- Every fppf covering family of the slice site admits an étale refinement by finite morphisms,
in the existential shape of `TopologyComparison.Situation.tau_covering_refinement`. -/
@[stacks 0F0H "(5) covering refinement"]
theorem tau_covering_refinement {U : Scheme.{u}} {ι : Type i} (cover : ι → Over U)
    (hcover : (fppfTopology.over U).CoversTop cover) :
    ∃ (J : Type (max (u + 1) i)) (V : J → Over U),
      (etaleTopology.over U).CoversTop V ∧
        ∃ (W : J → Scheme.{u}) (f : ∀ idx, W idx ⟶ (V idx).left),
          ∀ idx,
            IsFinite (f idx) ∧
              Sieve.generate (Presieve.singleton (f idx)) ∈ fppfTopology (V idx).left ∧
                ∃ (Kidx : Type (max (u + 1) i)) (Wcover : Kidx → Over (W idx)),
                  (etaleTopology.over (W idx)).CoversTop Wcover ∧
                    ∀ a : Kidx,
                      ∃ b : ι,
                        Nonempty
                          ((Over.mk ((Wcover a).hom ≫ f idx ≫ (V idx).hom)) ⟶ cover b) := sorry

/-- Inverse image along a morphism of schemes preserves the essential-image coefficient family. -/
@[stacks 0F0H "(2) inverse-image closure"]
theorem essImageAb_inverseImage_mem
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {ℱ : Sheaf (etaleTopology.over Y) AddCommGrpCat.{u + 1}}
    (hℱ : essImageAb Y ℱ) :
    essImageAb X ((etaleTopology.overMapPullback AddCommGrpCat.{u + 1} f).obj ℱ) := sorry

/-- An essential-image coefficient sheaf on the big étale site is an fppf sheaf. -/
@[stacks 0F0H "(3) fppf sheaf condition"]
theorem essImageAb_isSheafFppf
    {X : Scheme.{u}} {ℱ : Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1}}
    (hℱ : essImageAb X ℱ) :
    Presheaf.IsSheaf (fppfTopology.over X) ℱ.1 := sorry

/-- Higher direct images along a finite morphism preserve the essential-image coefficient family. -/
@[stacks 0F0H "(4) higher direct image closure"]
theorem essImageAb_higherDirectImage_mem
    [∀ X : Scheme.{u}, HasSheafify (etaleTopology.over X) AddCommGrpCat.{u + 1}]
    [∀ X : Scheme.{u},
      HasInjectiveResolutions (Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1})]
    [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      Functor.Additive
        ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          (etaleTopology.over X) (etaleTopology.over Y))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [hf : IsFinite f] (n : ℕ)
    {ℱ : Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1}}
    (hℱ : essImageAb X ℱ) :
    essImageAb Y
      ((((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          (etaleTopology.over X) (etaleTopology.over Y)).rightDerived n).obj ℱ) := sorry

/-- The fppf/étale comparison on `Scheme`, with morphism property `IsFinite` and coefficient
family `essImageAb`, satisfies the conditions of `TopologyComparison.Situation`. -/
@[stacks 0F0H]
instance comparisonSituation :
    TopologyComparison.Situation.{u + 1, u, u + 1, u + 1, u + 1}
      fppfTopology etaleTopology @IsFinite
      (fun X : Scheme.{u} ↦ essImageAb X) where
  isWeakSerre X := essImageAb_isWeakSerre X
  hasPullbacks := inferInstance
  isStableUnderBaseChange := inferInstance
  inverseImage_mem := essImageAb_inverseImage_mem
  isSheaf_for_finer_topology := essImageAb_isSheafFppf
  higherDirectImage_mem := by
    intro _ _ _ X Y f hf n ℱ hℱ
    exact essImageAb_higherDirectImage_mem f (hf := hf) n hℱ
  tau_covering_refinement := tau_covering_refinement

end AlgebraicGeometry.Scheme.FppfEtale

end
