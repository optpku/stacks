/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Augment
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Topology.Sets.OpenCover
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CompactSupport.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.OpenImmersion

/-!
# Čech chain complex of locally quasi-finite lower shrieks

An indexed family of Zariski opens on the source of a locally quasi-finite
morphism determines a functorial augmented chain complex of abelian étale
sheaves on the target, with coproduct terms `f_{∩σ,!}(F|_{∩σ})` and
augmentation `f_! F`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open AlgebraicGeometry AlgebraicGeometry.Scheme
open TopologicalSpace
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasCoproducts.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
variable {ι : Type u} (𝒰 : ι → X.Opens)

/-- The Čech intersection of the members of an indexed open family selected by
a finite tuple. -/
abbrev lowerShriekCechIntersection {n : ℕ} (σ : Fin n → ι) : X.Opens :=
  ⨅ a, 𝒰 (σ a)

/-- Omitting one index enlarges a Čech intersection. -/
theorem lowerShriekCechIntersection_le_succAbove {n : ℕ}
    (σ : Fin (n + 1) → ι) (j : Fin (n + 1)) :
    lowerShriekCechIntersection 𝒰 σ ≤
      lowerShriekCechIntersection 𝒰 (σ ∘ j.succAboveEmb) :=
  sorry

/-- The open immersion of Čech intersections obtained by omitting one index. -/
abbrev lowerShriekCechInclusion {n : ℕ} (σ : Fin (n + 1) → ι) (j : Fin (n + 1)) :
    (lowerShriekCechIntersection 𝒰 σ : Scheme.{u}) ⟶
      (lowerShriekCechIntersection 𝒰 (σ ∘ j.succAboveEmb) : Scheme.{u}) :=
  X.homOfLE (lowerShriekCechIntersection_le_succAbove 𝒰 σ j)

/-- Composing the omitted-index open immersion with the restricted structure
map recovers the structure map of the smaller intersection. -/
theorem lowerShriekCechIntersection_ι_comp {n : ℕ} (σ : Fin (n + 1) → ι)
    (j : Fin (n + 1)) :
    lowerShriekCechInclusion 𝒰 σ j ≫
        (lowerShriekCechIntersection 𝒰 (σ ∘ j.succAboveEmb)).ι ≫ f =
      (lowerShriekCechIntersection 𝒰 σ).ι ≫ f :=
  sorry

/-- One multi-index compact-support direct image `f_{σ,!}(F|_σ)`. -/
def lowerShriekCechSummand (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (n : ℕ) (σ : Fin (n + 1) → ι) :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
  (lowerShriek ((lowerShriekCechIntersection 𝒰 σ).ι ≫ f)).obj
    ((etaleRestrictionSheaf (lowerShriekCechIntersection 𝒰 σ).ι
        AddCommGrpCat.{u}).obj F)

/-- The coproduct of compact-support direct images over all tuples of a fixed
length. -/
def lowerShriekCechTerm (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (n : ℕ) : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
  ∐ lowerShriekCechSummand f 𝒰 F n

/-- The coproduct inclusion of one multi-index summand. -/
abbrev lowerShriekCechTerm_ι (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (n : ℕ) (σ : Fin (n + 1) → ι) :
    lowerShriekCechSummand f 𝒰 F n σ ⟶ lowerShriekCechTerm f 𝒰 F n :=
  Sigma.ι (lowerShriekCechSummand f 𝒰 F n) σ

/-- Restriction of `F` to a Čech intersection identifies with restriction to
the omitted-index intersection followed by restriction along the inclusion. -/
def lowerShriekCechRestrictionIso
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {n : ℕ}
    (σ : Fin (n + 1) → ι) (j : Fin (n + 1)) :
    (etaleRestrictionSheaf (lowerShriekCechIntersection 𝒰 σ).ι
        AddCommGrpCat.{u}).obj F ≅
      (etaleRestrictionSheaf (lowerShriekCechInclusion 𝒰 σ j)
          AddCommGrpCat.{u}).obj
        ((etaleRestrictionSheaf
            (lowerShriekCechIntersection 𝒰 (σ ∘ j.succAboveEmb)).ι
            AddCommGrpCat.{u}).obj F) :=
  etaleRestrictionSheaf_opensLe F (lowerShriekCechIntersection_le_succAbove 𝒰 σ j)

/-- The canonical open-immersion covariance map for the face that omits index `j`. -/
def lowerShriekCechFace (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {n : ℕ} (σ : Fin (n + 2) → ι) (j : Fin (n + 2)) :
    lowerShriekCechSummand f 𝒰 F (n + 1) σ ⟶
      lowerShriekCechSummand f 𝒰 F n (σ ∘ j.succAboveEmb) :=
  (lowerShriek ((lowerShriekCechIntersection 𝒰 σ).ι ≫ f)).map
      (lowerShriekCechRestrictionIso 𝒰 F σ j).hom ≫
    (lowerShriekCongr
        (lowerShriekCechIntersection_ι_comp f 𝒰 σ j).symm).hom.app
      ((etaleRestrictionSheaf (lowerShriekCechInclusion 𝒰 σ j)
          AddCommGrpCat.{u}).obj
        ((etaleRestrictionSheaf
            (lowerShriekCechIntersection 𝒰 (σ ∘ j.succAboveEmb)).ι
            AddCommGrpCat.{u}).obj F)) ≫
    (lowerShriekOpenImmersion (lowerShriekCechInclusion 𝒰 σ j)
        ((lowerShriekCechIntersection 𝒰 (σ ∘ j.succAboveEmb)).ι ≫ f)).app
      ((etaleRestrictionSheaf
          (lowerShriekCechIntersection 𝒰 (σ ∘ j.succAboveEmb)).ι
          AddCommGrpCat.{u}).obj F)

/-- The alternating Čech differential on coproducts of lower shrieks. -/
def lowerShriekCechDifferential (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (n : ℕ) : lowerShriekCechTerm f 𝒰 F (n + 1) ⟶ lowerShriekCechTerm f 𝒰 F n :=
  Sigma.desc fun σ ↦
    ∑ j : Fin (n + 2),
      (-1 : ℤ) ^ (j : ℕ) •
        (lowerShriekCechFace f 𝒰 F σ j ≫
          lowerShriekCechTerm_ι f 𝒰 F n (σ ∘ j.succAboveEmb))

/-- Consecutive Čech differentials of lower shrieks compose to zero. -/
theorem lowerShriekCechDifferential_comp
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    lowerShriekCechDifferential f 𝒰 F (n + 1) ≫
      lowerShriekCechDifferential f 𝒰 F n = 0 :=
  sorry

/-- The unaugmented Čech chain complex of compact-support direct images. -/
def lowerShriekCechComplex (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    ChainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ℕ :=
  ChainComplex.of (lowerShriekCechTerm f 𝒰 F) (lowerShriekCechDifferential f 𝒰 F)
    (lowerShriekCechDifferential_comp f 𝒰 F)

/-- Objects of the unaugmented complex are the Čech coproduct terms. -/
theorem lowerShriekCechComplex_X
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    (lowerShriekCechComplex f 𝒰 F).X n = lowerShriekCechTerm f 𝒰 F n :=
  sorry

/-- Differentials of the unaugmented complex are the Čech differentials. -/
theorem lowerShriekCechComplex_d
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    (lowerShriekCechComplex f 𝒰 F).d (n + 1) n =
      lowerShriekCechDifferential f 𝒰 F n :=
  sorry

/-- A morphism of abelian étale sheaves acts on one Čech summand. -/
def lowerShriekCechSummandMap {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (φ : F ⟶ G) (n : ℕ) (σ : Fin (n + 1) → ι) :
    lowerShriekCechSummand f 𝒰 F n σ ⟶ lowerShriekCechSummand f 𝒰 G n σ :=
  (lowerShriek ((lowerShriekCechIntersection 𝒰 σ).ι ≫ f)).map
    ((etaleRestrictionSheaf (lowerShriekCechIntersection 𝒰 σ).ι
        AddCommGrpCat.{u}).map φ)

/-- A morphism of abelian étale sheaves acts on a Čech coproduct term. -/
def lowerShriekCechTermMap {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (φ : F ⟶ G) (n : ℕ) :
    lowerShriekCechTerm f 𝒰 F n ⟶ lowerShriekCechTerm f 𝒰 G n :=
  Limits.Sigma.map (lowerShriekCechSummandMap f 𝒰 φ n)

/-- The augmentation from the degree-zero coproduct to `f_! F`. -/
def lowerShriekCechAugmentation
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    lowerShriekCechTerm f 𝒰 F 0 ⟶ (lowerShriek f).obj F :=
  Sigma.desc fun σ ↦
    (lowerShriekOpenImmersion_opens (lowerShriekCechIntersection 𝒰 σ) f).app F

/-- The augmentation annihilates the first unaugmented differential. -/
theorem lowerShriekCechAugmentation_comp
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriekCechComplex f 𝒰 F).d 1 0 ≫
      lowerShriekCechAugmentation f 𝒰 F = 0 :=
  sorry

/-- The augmented Čech chain complex of compact-support direct images, with
`f_! F` in degree zero. -/
def lowerShriekCechAugmentedComplex
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    ChainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ℕ :=
  ChainComplex.augment (lowerShriekCechComplex f 𝒰 F)
    (lowerShriekCechAugmentation f 𝒰 F)
    (lowerShriekCechAugmentation_comp f 𝒰 F)

/-- Degree zero of the augmented complex is `f_! F`. -/
theorem lowerShriekCechAugmentedComplex_X_zero
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriekCechAugmentedComplex f 𝒰 F).X 0 = (lowerShriek f).obj F :=
  sorry

/-- Positive-degree objects of the augmented complex are the unaugmented Čech
coproduct terms. -/
theorem lowerShriekCechAugmentedComplex_X_succ
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    (lowerShriekCechAugmentedComplex f 𝒰 F).X (n + 1) =
      lowerShriekCechTerm f 𝒰 F n :=
  sorry

/-- The degree-zero differential of the augmented complex is the augmentation. -/
theorem lowerShriekCechAugmentedComplex_d_one_zero
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriekCechAugmentedComplex f 𝒰 F).d 1 0 =
      lowerShriekCechAugmentation f 𝒰 F :=
  sorry

/-- A morphism of abelian étale sheaves induces a morphism of augmented Čech
complexes. -/
def lowerShriekCechAugmentedComplexMap
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) :
    lowerShriekCechAugmentedComplex f 𝒰 F ⟶
      lowerShriekCechAugmentedComplex f 𝒰 G where
  f
    | 0 => (lowerShriek f).map φ
    | n + 1 => lowerShriekCechTermMap f 𝒰 φ n
  comm' := sorry

/-- The functor sending an abelian étale sheaf to its augmented Čech complex of
compact-support direct images. -/
def lowerShriekCechAugmentedComplexFunctor :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      ChainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ℕ where
  obj := lowerShriekCechAugmentedComplex f 𝒰
  map := lowerShriekCechAugmentedComplexMap f 𝒰
  map_id := sorry
  map_comp := sorry

/-- Evaluating the Čech functor recovers the augmented complex. -/
theorem lowerShriekCechAugmentedComplexFunctor_obj
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriekCechAugmentedComplexFunctor f 𝒰).obj F =
      lowerShriekCechAugmentedComplex f 𝒰 F :=
  sorry

/-- The Čech functor acts on morphisms by the degreewise coproduct maps. -/
theorem lowerShriekCechAugmentedComplexFunctor_map
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) :
    (lowerShriekCechAugmentedComplexFunctor f 𝒰).map φ =
      lowerShriekCechAugmentedComplexMap f 𝒰 φ :=
  sorry


/-- Let `f : X ⟶ Y` be a locally quasi-finite morphism of
schemes that is locally of finite type, and let `𝒰 : ι → X.Opens` be an open covering of `X`. Then for
`F` in `Ab(X_étale)` the functorial augmented Čech chain complex
`lowerShriekCechAugmentedComplex f 𝒰 F`, with coproduct terms
`lowerShriekCechTerm f 𝒰 F n` of summands `f_{∩σ,!}(F|_{∩σ})` and
augmentation `f_! F`, is acyclic. -/
@[stacks 0F5H]
theorem lowerShriekCechAugmentedComplex_acyclic {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasCoproducts.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
    {ι : Type u} (𝒰 : ι → X.Opens) (h𝒰 : IsOpenCover 𝒰)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriekCechAugmentedComplex f 𝒰 F).Acyclic :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
