module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.CategoryTheory.Sites.EnoughObjects.Presentation
public import ReasLib.CategoryTheory.Sites.FiniteRefinement
public import ReasLib.CategoryTheory.Sites.FilteredColimit.GlobalSections
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Coproduct
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Cover

/-!
# Quasi-compact test sets from representable sheaves

This file collects reusable finite-basis hypotheses producing a quasi-compact
test set of sheaves. The underlying coproduct is owned by the general
`sheafifiedRepresentableCoproduct` API; finiteness remains a property of the
families selected by this test-set construction.
-/

@[expose] public section

noncomputable section

universe u v

namespace CategoryTheory.GrothendieckTopology.QuasiCompact.TestSet

open Limits Sheaf SemiRepresentableFamily.Over

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type (max u v))]

/-- A sheaf is, up to isomorphism, a finite coproduct of sheafified
representables indexed by objects of `B`. -/
def isFiniteRepresentableCoproduct (B : Set C)
    (F : Sheaf J (Type (max u v))) : Prop :=
  ∃ 𝒰 : Limits.FormalCoproduct.{max u v} C, ∃ _ : Finite 𝒰.index,
    (∀ i : 𝒰.index, 𝒰.obj i ∈ B) ∧
      Nonempty (F ≅ J.sheafifiedRepresentableCoproduct 𝒰)

/-- The isomorphism-stable collection of finite coproducts of sheafified
representables indexed by `B`. -/
def finiteRepresentableCoproducts (B : Set C) :
    Set (Sheaf J (Type (max u v))) :=
  {F | isFiniteRepresentableCoproduct J B F}

/-- Membership in `finiteRepresentableCoproducts` is its defining finite
representable-coproduct property. -/
theorem mem_finiteRepresentableCoproducts_iff (B : Set C)
    (F : Sheaf J (Type (max u v))) :
    F ∈ finiteRepresentableCoproducts J B ↔
      isFiniteRepresentableCoproduct J B F := sorry

/-- A basis whose finite representable coproducts test locally surjective maps
to the terminal sheaf and whose pairwise representable products are
quasi-compact. -/
class SurjectiveBasis (B : Set C) : Prop where
  /-- Locally surjective maps to the terminal sheaf admit a locally surjective
  map from a finite representable coproduct indexed by `B`. -/
  surjective_to_terminal {F : Sheaf J (Type (max u v))}
      (hF : Sheaf.IsLocallySurjective (terminal.from F)) :
      ∃ 𝒰 : Limits.FormalCoproduct.{max u v} C, ∃ _ : Finite 𝒰.index,
        (∀ i : 𝒰.index, 𝒰.obj i ∈ B) ∧
          ∃ κ : J.sheafifiedRepresentableCoproduct 𝒰 ⟶ F,
            Sheaf.IsLocallySurjective (κ ≫ terminal.from F)
  /-- Pairwise products of representables indexed by `B` are quasi-compact. -/
  product_quasiCompact {U V : C} (hU : U ∈ B) (hV : V ∈ B) :
    ((J.sheafifiedRepresentable U) ⨯
      (J.sheafifiedRepresentable V)).IsQuasiCompactObject

/-- The source-semantic clauses of a surjective basis. -/
theorem SurjectiveBasis.spec (B : Set C) [SurjectiveBasis J B] :
    (∀ {F : Sheaf J (Type (max u v))},
      Sheaf.IsLocallySurjective (terminal.from F) →
        ∃ 𝒰 : Limits.FormalCoproduct.{max u v} C, ∃ _ : Finite 𝒰.index,
          (∀ i : 𝒰.index, 𝒰.obj i ∈ B) ∧
            ∃ κ : J.sheafifiedRepresentableCoproduct 𝒰 ⟶ F,
              Sheaf.IsLocallySurjective (κ ≫ terminal.from F)) ∧
      (∀ {U V : C}, U ∈ B → V ∈ B →
        ((J.sheafifiedRepresentable U) ⨯
          (J.sheafifiedRepresentable V)).IsQuasiCompactObject) := sorry

/-- A basis with a finite terminal cover, finite refinements by basis objects,
and finite product covers by basis objects. -/
class RefiningBasis (B : Set C) : Prop where
  /-- The terminal sheaf has a locally surjective finite representable cover
  indexed by `B`. -/
  terminal_surjection :
    ∃ 𝒰 : Limits.FormalCoproduct.{max u v} C, ∃ _ : Finite 𝒰.index,
      (∀ i : 𝒰.index, 𝒰.obj i ∈ B) ∧
        Sheaf.IsLocallySurjective
          (terminal.from (J.sheafifiedRepresentableCoproduct 𝒰))
  /-- Every cover of a basis object has a finite refinement by basis objects. -/
  cover_refinement {U : C} (hU : U ∈ B)
      (𝒰 : SemiRepresentableFamily.Over.{max u v} U) (h𝒰 : 𝒰.toSieve ∈ J U) :
      ∃ 𝒱 : SemiRepresentableFamily.Over.{max u v} U, ∃ _ : Finite 𝒱.index,
        ∃ _ : 𝒱 ⟶ 𝒰, 𝒱.toSieve ∈ J U ∧
          ∀ j : 𝒱.index, (𝒱.obj j).left ∈ B
  /-- Pairwise products of basis representables have finite locally surjective
  covers by basis representables. -/
  product_surjection {U V : C} (hU : U ∈ B) (hV : V ∈ B) :
    ∃ 𝒱 : Limits.FormalCoproduct.{max u v} C, ∃ _ : Finite 𝒱.index,
      ∃ f : ∀ i : 𝒱.index, 𝒱.obj i ⟶ U,
        ∃ g : ∀ i : 𝒱.index, 𝒱.obj i ⟶ V,
          (∀ i : 𝒱.index, 𝒱.obj i ∈ B) ∧
            Sheaf.IsLocallySurjective
              (prod.lift
                (Limits.Sigma.desc
                  (fun i : 𝒱.index ↦ J.sheafifiedRepresentableMap (f i)))
                (Limits.Sigma.desc
                  (fun i : 𝒱.index ↦ J.sheafifiedRepresentableMap (g i))))

/-- The source-semantic clauses of a refining basis. -/
theorem RefiningBasis.spec (B : Set C) [RefiningBasis J B] :
    (∃ 𝒰 : Limits.FormalCoproduct.{max u v} C, ∃ _ : Finite 𝒰.index,
      (∀ i : 𝒰.index, 𝒰.obj i ∈ B) ∧
        Sheaf.IsLocallySurjective
          (terminal.from (J.sheafifiedRepresentableCoproduct 𝒰))) ∧
      (∀ {U : C}, U ∈ B →
        ∀ (𝒰 : SemiRepresentableFamily.Over.{max u v} U), 𝒰.toSieve ∈ J U →
          ∃ 𝒱 : SemiRepresentableFamily.Over.{max u v} U, ∃ _ : Finite 𝒱.index,
            ∃ _ : 𝒱 ⟶ 𝒰, 𝒱.toSieve ∈ J U ∧
              ∀ j : 𝒱.index, (𝒱.obj j).left ∈ B) ∧
      (∀ {U V : C}, U ∈ B → V ∈ B →
        ∃ 𝒱 : Limits.FormalCoproduct.{max u v} C, ∃ _ : Finite 𝒱.index,
          ∃ f : ∀ i : 𝒱.index, 𝒱.obj i ⟶ U,
            ∃ g : ∀ i : 𝒱.index, 𝒱.obj i ⟶ V,
              (∀ i : 𝒱.index, 𝒱.obj i ∈ B) ∧
                Sheaf.IsLocallySurjective
                  (prod.lift
                    (Limits.Sigma.desc
                      (fun i : 𝒱.index ↦ J.sheafifiedRepresentableMap (f i)))
                    (Limits.Sigma.desc
                      (fun i : 𝒱.index ↦ J.sheafifiedRepresentableMap (g i))))) := sorry

/-- Products of sheafified representables of quasi-compact site objects are
quasi-compact in the sheaf category. -/
class QuasiCompactRepresentableProducts : Prop where
  /-- Quasi-compactness of pairwise products of quasi-compact representables. -/
  product_quasiCompact {U V : C}
      (hU : J.QuasiCompactObject U) (hV : J.QuasiCompactObject V) :
      ((J.sheafifiedRepresentable U) ⨯
        (J.sheafifiedRepresentable V)).IsQuasiCompactObject

/-- A quasi-compact terminal sheaf, enough quasi-compact site objects, and
quasi-compact pairwise representable products. -/
class GeneratorHypotheses : Prop where
  /-- The terminal sheaf is quasi-compact. -/
  topos_quasiCompact :
    (⊤_ (Sheaf J (Type (max u v)))).IsQuasiCompactObject
  /-- Quasi-compact objects cover the site. -/
  enough_quasiCompactObjects :
    J.HasEnoughObjectsWithProperty J.QuasiCompactObject
  /-- Products of quasi-compact representables are quasi-compact. -/
  quasiCompactRepresentableProducts :
    QuasiCompactRepresentableProducts J

/-- The source-semantic clauses of the quasi-compact generator hypothesis. -/
theorem GeneratorHypotheses.spec [GeneratorHypotheses J] :
    (⊤_ (Sheaf J (Type (max u v)))).IsQuasiCompactObject ∧
      J.HasEnoughObjectsWithProperty J.QuasiCompactObject ∧
        QuasiCompactRepresentableProducts J := sorry

/-- A surjective basis produces a quasi-compact test set of finite
representable coproducts. -/
theorem SurjectiveBasis.isQuasiCompactTestSet
    (B : Set C) [SurjectiveBasis J B] :
    IsQuasiCompactTestSet J (finiteRepresentableCoproducts J B) := sorry

/-- Each object of a refining basis has the finite-refinement property. -/
theorem RefiningBasis.finiteRefinement
    {B : Set C} [RefiningBasis J B] {U : C} (hU : U ∈ B) :
    HasFiniteRefinement J U := sorry

/-- A refining basis produces a quasi-compact test set of finite
representable coproducts. -/
theorem RefiningBasis.isQuasiCompactTestSet
    (B : Set C) [RefiningBasis J B] :
    IsQuasiCompactTestSet J (finiteRepresentableCoproducts J B) := sorry

/-- Quasi-compact generators and quasi-compact pairwise representable products
produce the surjective-basis hypothesis for all quasi-compact objects. -/
theorem surjectiveBasis_of_generators
    (hTopos : (⊤_ (Sheaf J (Type (max u v)))).IsQuasiCompactObject)
    (hEnough : J.HasEnoughObjectsWithProperty J.QuasiCompactObject)
    [QuasiCompactRepresentableProducts J] :
    SurjectiveBasis J {U | J.QuasiCompactObject U} := sorry

/-- Quasi-compact generators produce a quasi-compact test set of finite
representable coproducts. -/
theorem isQuasiCompactTestSet_of_generators
    (hTopos : (⊤_ (Sheaf J (Type (max u v)))).IsQuasiCompactObject)
    (hEnough : J.HasEnoughObjectsWithProperty J.QuasiCompactObject)
    [QuasiCompactRepresentableProducts J] :
    IsQuasiCompactTestSet J
      (finiteRepresentableCoproducts J {U | J.QuasiCompactObject U}) := sorry

/-- Remark 7.17.9 (0GMS): any of the standard finite-basis or
quasi-compact-generator packages supplies a quasi-compact test set. -/
@[stacks 0GMS]
theorem exists_of_cases
    (h_cases :
      (∃ B : Set C, SurjectiveBasis J B) ∨
        (∃ B : Set C, RefiningBasis J B) ∨ GeneratorHypotheses J) :
    ∃ S : Set (Sheaf J (Type (max u v))), IsQuasiCompactTestSet J S := sorry

/-- Package the three source cases as the typeclass-friendly global-sections
test-set hypothesis. -/
theorem hasTestSet_of_cases
    (h_cases :
      (∃ B : Set C, SurjectiveBasis J B) ∨
        (∃ B : Set C, RefiningBasis J B) ∨ GeneratorHypotheses J) :
    QuasiCompact.HasTestSet J := sorry

end CategoryTheory.GrothendieckTopology.QuasiCompact.TestSet
