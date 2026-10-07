module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Sites.Abelian
public import stacks_project.Chap63.Lemma_63_4_7_Cech
public import stacks_project.Chap63.Remark_63_3_5_Covariance_with_respect_to_open_embeddings_OpenImmersion

/-!
# Separated Čech terms of étale lower shriek

An open family with separated restrictions of a locally quasi-finite morphism
determines coproduct terms `f_{σ,!}(F|_σ)` using the separated construction
`etaleLowerShriek`, together with the penultimate Čech map on those terms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasCoproducts.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
variable {ι : Type u} (𝒰 : ι → X.Opens)
variable [∀ i, IsSeparated ((𝒰 i).ι ≫ f)]

/-- Finite Čech intersections of a separated-restriction open family remain
separated over the target. -/
instance isSeparated_lowerShriekCechIntersection {n : ℕ}
    (σ : Fin (n + 1) → ι) :
    IsSeparated ((lowerShriekCechIntersection 𝒰 σ).ι ≫ f) :=
  sorry

/-- One multi-index compact-support direct image `f_{σ,!}(F|_σ)` formed with
the separated functor `etaleLowerShriek`. -/
def etaleLowerShriekCechSummand
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ)
    (σ : Fin (n + 1) → ι) :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
  (etaleLowerShriek ((lowerShriekCechIntersection 𝒰 σ).ι ≫ f)).obj
    ((etaleRestrictionSheaf (lowerShriekCechIntersection 𝒰 σ).ι
        AddCommGrpCat.{u}).obj F)

/-- The coproduct of separated compact-support direct images over all tuples of
a fixed length. -/
def etaleLowerShriekCechTerm
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
  ∐ etaleLowerShriekCechSummand f 𝒰 F n

/-- The coproduct inclusion of one multi-index separated summand. -/
abbrev etaleLowerShriekCechTerm_ι
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ)
    (σ : Fin (n + 1) → ι) :
    etaleLowerShriekCechSummand f 𝒰 F n σ ⟶ etaleLowerShriekCechTerm f 𝒰 F n :=
  Sigma.ι (etaleLowerShriekCechSummand f 𝒰 F n) σ

/-- The covariance map of Remark 63.3.5 for the face that omits index `j`. -/
def etaleLowerShriekCechFace
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {n : ℕ}
    (σ : Fin (n + 2) → ι) (j : Fin (n + 2)) :
    etaleLowerShriekCechSummand f 𝒰 F (n + 1) σ ⟶
      etaleLowerShriekCechSummand f 𝒰 F n (σ ∘ j.succAboveEmb) :=
  (etaleLowerShriek ((lowerShriekCechIntersection 𝒰 σ).ι ≫ f)).map
      (lowerShriekCechRestrictionIso 𝒰 F σ j).hom ≫
    (etaleLowerShriekCongr
        (lowerShriekCechIntersection_ι_comp f 𝒰 σ j).symm).hom.app
      ((etaleRestrictionSheaf (lowerShriekCechInclusion 𝒰 σ j)
          AddCommGrpCat.{u}).obj
        ((etaleRestrictionSheaf
            (lowerShriekCechIntersection 𝒰 (σ ∘ j.succAboveEmb)).ι
            AddCommGrpCat.{u}).obj F)) ≫
    (etaleLowerShriekOpenImmersion (lowerShriekCechInclusion 𝒰 σ j)
        ((lowerShriekCechIntersection 𝒰 (σ ∘ j.succAboveEmb)).ι ≫ f)).app
      ((etaleRestrictionSheaf
          (lowerShriekCechIntersection 𝒰 (σ ∘ j.succAboveEmb)).ι
          AddCommGrpCat.{u}).obj F)

/-- The penultimate Čech map
`⊕_{i0,i1} f_{i0 i1,!}(F|_{X_{i0 i1}}) ⟶ ⊕_{i0} f_{i0,!}(F|_{X_{i0}})`
of separated compact-support direct images. -/
def etaleLowerShriekCechPenultimate
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleLowerShriekCechTerm f 𝒰 F 1 ⟶ etaleLowerShriekCechTerm f 𝒰 F 0 :=
  Sigma.desc fun σ ↦
    ∑ j : Fin 2,
      (-1 : ℤ) ^ (j : ℕ) •
        (etaleLowerShriekCechFace f 𝒰 F σ j ≫
          etaleLowerShriekCechTerm_ι f 𝒰 F 0 (σ ∘ j.succAboveEmb))

/-- A morphism of abelian étale sheaves acts on one separated Čech summand. -/
def etaleLowerShriekCechSummandMap
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G)
    (n : ℕ) (σ : Fin (n + 1) → ι) :
    etaleLowerShriekCechSummand f 𝒰 F n σ ⟶
      etaleLowerShriekCechSummand f 𝒰 G n σ :=
  (etaleLowerShriek ((lowerShriekCechIntersection 𝒰 σ).ι ≫ f)).map
    ((etaleRestrictionSheaf (lowerShriekCechIntersection 𝒰 σ).ι
        AddCommGrpCat.{u}).map φ)

/-- A morphism of abelian étale sheaves acts on a separated Čech coproduct
term. -/
def etaleLowerShriekCechTermMap
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G)
    (n : ℕ) :
    etaleLowerShriekCechTerm f 𝒰 F n ⟶ etaleLowerShriekCechTerm f 𝒰 G n :=
  Limits.Sigma.map (etaleLowerShriekCechSummandMap f 𝒰 φ n)

/-- The penultimate map is natural in the abelian étale sheaf. -/
theorem etaleLowerShriekCechPenultimate_naturality
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) :
    etaleLowerShriekCechPenultimate f 𝒰 F ≫
        etaleLowerShriekCechTermMap f 𝒰 φ 0 =
      etaleLowerShriekCechTermMap f 𝒰 φ 1 ≫
        etaleLowerShriekCechPenultimate f 𝒰 G :=
  sorry

/-- Evaluating a separated Čech summand recovers `etaleLowerShriek` of the
restricted sheaf. -/
theorem etaleLowerShriekCechSummand_obj
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ)
    (σ : Fin (n + 1) → ι) :
    etaleLowerShriekCechSummand f 𝒰 F n σ =
      (etaleLowerShriek ((lowerShriekCechIntersection 𝒰 σ).ι ≫ f)).obj
        ((etaleRestrictionSheaf (lowerShriekCechIntersection 𝒰 σ).ι
            AddCommGrpCat.{u}).obj F) :=
  sorry

/-- Evaluating a separated Čech term recovers the coproduct of the summands. -/
theorem etaleLowerShriekCechTerm_obj
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    etaleLowerShriekCechTerm f 𝒰 F n = ∐ etaleLowerShriekCechSummand f 𝒰 F n :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
