module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Comparison
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Situation
public import stacks_project.Chap59.Lemma_59_100_5_Coefficients
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fppf/étale topology-comparison situation

This leaf owns the `TopologyComparison.Situation` instance comparing the big fppf and étale
topologies on schemes, with morphism property `IsFinite` and coefficient family `essImageAb`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale.SmallToBig
open AlgebraicGeometry.Scheme.FppfEtale
open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.GrothendieckTopology
open CategoryTheory.MorphismProperty

noncomputable section

universe u i j k

namespace AlgebraicGeometry.Scheme.FppfEtale

/-- Every fppf covering family of the slice site admits an étale refinement by finite morphisms,
in the existential shape of `TopologyComparison.Situation.tau_covering_refinement`. -/
@[stacks 0F0H "(5) covering refinement"]
theorem tau_covering_refinement {U : Scheme.{u}} {ι : Type i} (cover : ι → Over U)
    (hcover : (fppfTopology.over U).CoversTop cover) :
    ∃ (J : Type j) (V : J → Over U),
      (etaleTopology.over U).CoversTop V ∧
        ∃ (W : J → Scheme.{u}) (f : ∀ idx, W idx ⟶ (V idx).left),
          ∀ idx,
            IsFinite (f idx) ∧
              Sieve.generate (Presieve.singleton (f idx)) ∈ fppfTopology (V idx).left ∧
                ∃ (Kidx : Type k) (Wcover : Kidx → Over (W idx)),
                  (etaleTopology.over (W idx)).CoversTop Wcover ∧
                    ∀ a : Kidx,
                      ∃ b : ι,
                        Nonempty
                          ((Over.mk ((Wcover a).hom ≫ f idx ≫ (V idx).hom)) ⟶ cover b) := sorry

variable [∀ (X : Scheme.{u}) (P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
    (relocalizationFunctor (𝟙 X)).op.HasLeftKanExtension P]

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
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (n : ℕ)
    {ℱ : Sheaf (etaleTopology.over X) AddCommGrpCat.{u + 1}}
    (hℱ : essImageAb X ℱ) :
    essImageAb Y
      ((((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          (etaleTopology.over X) (etaleTopology.over Y)).rightDerived n).obj ℱ) := sorry

/-- The fppf/étale comparison on `Scheme`, with morphism property `IsFinite` and coefficient
family `essImageAb`, satisfies the conditions of `TopologyComparison.Situation`. -/
@[stacks 0F0H, instance]
instance comparisonSituation :
    TopologyComparison.Situation fppfTopology etaleTopology @IsFinite
      (fun X : Scheme.{u} ↦ essImageAb X) := sorry

end AlgebraicGeometry.Scheme.FppfEtale

end
