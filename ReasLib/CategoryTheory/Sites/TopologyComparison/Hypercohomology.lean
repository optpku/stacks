/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.TopologyComparison.Situation
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Derived
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Cohomology
public import ReasLib.CategoryTheory.DerivedCategory.Preimage.Homology
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Hypercohomology under a topology comparison

The comparison-situation data and the derived inverse image are owned by the topology-comparison
leaves.  This file owns the source-facing hypercohomology consequence, so chapter files can use a
recall block without importing another chapter.
-/

open CategoryTheory CategoryTheory.Limits
open DerivedCategory
open scoped CategoryTheory CategoryTheory.GrothendieckTopology
  DerivedCategory.CohomologyIn GrothendieckTopology GrothendieckTopologyDerivedSections

noncomputable section

universe u v

namespace CategoryTheory.GrothendieckTopology.TopologyComparison.Hypercohomology

variable {C : Type u} [Category.{v} C]
variable {τ τ' : GrothendieckTopology C}

section

variable (hle : τ' ≤ τ)
variable (P : MorphismProperty C)
variable (A' : ∀ X : C,
  ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))

variable [∀ X : C, HasWeakSheafify (τ'.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, HasExt (Sheaf (τ.over X) AddCommGrpCat.{max u v})]
variable [∀ X : C,
  HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]
variable [∀ X : C, IsGrothendieckAbelian (SiteAbelianSheafCat (τ.over X))]
variable [∀ X : C, IsGrothendieckAbelian (SiteAbelianSheafCat (τ'.over X))]

/-- Lemma 21.30.4 (0EZB): in a topology-comparison situation, `(V_n)` and the source
cohomology range identify degree-`n` hypercohomology on the coarser site with the degree-`n`
hypercohomology after the canonical inverse image to the finer site.  The negative-degree and
`A'_X` hypotheses are kept in their source-facing form; downstream users may package them with
`DerivedCategory.IsGE` and `CohomologyIn` when that is more convenient.
-/
@[stacks 0EZB]
theorem isomorphic_of_conditionV
    (h : Situation τ τ' P A')
    (n : ℕ)
    (hVn : h.LocalVanishing n)
    (X : C)
    (L : DerivedCategory (SiteAbelianSheafCat (τ'.over X)))
    (hLneg : ∀ i : ℤ, i < 0 → IsZero ((homologyFunctor _ i).obj L))
    (hLA' : ∀ i : ℕ, i ≤ n → A' X ((homologyFunctor _ (i : ℤ)).obj L)) :
    IsIsomorphic
      ((homologyFunctor AddCommGrpCat.{max u v} (n : ℤ)).obj
        ((RΓ[τ'.over X](Over.mk (𝟙 X))).obj L))
      ((homologyFunctor AddCommGrpCat.{max u v} (n : ℤ)).obj
        ((RΓ[τ.over X](Over.mk (𝟙 X))).obj
          (((ε[hle]_(X)⁻¹).mapDerivedCategory).obj L))) := sorry

end

section Degreewise

variable (hle : τ' ≤ τ)
variable (P : MorphismProperty C)
variable (A' : ∀ X : C,
  ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
variable [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, HasExt (Sheaf (τ.over X) AddCommGrpCat.{max u v})]
variable [∀ X : C, HasExt (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]

/-- Lemma 21.30.10 (0EZH) (1): with the all-degree vanishing certificate from 0EZF, the canonical
coarse-to-fine cohomology map for a selected coefficient sheaf is invertible in every degree. -/
@[stacks 0EZH "(1)"]
theorem pullbackMap_isIso_of_mem
    (h : Situation τ τ' P A')
    (hV : Situation.AllVanishing h)
    (X : C)
    (F' : Sheaf (τ'.over X) AddCommGrpCat.{max u v})
    (hF' : A' X F')
    (n : ℕ) :
    IsIso (Cohomology.pullbackMap hle X F' n) := sorry

/-- The objectwise `IsIsomorphic` view of `pullbackMap_isIso_of_mem`, retaining the same vanishing
certificate as the canonical map statement. -/
@[stacks 0EZH "(1), objectwise view"]
theorem cohomology_isomorphic_of_mem
    (h : Situation τ τ' P A')
    (hV : Situation.AllVanishing h)
    (X : C)
    (F' : Sheaf (τ'.over X) AddCommGrpCat.{max u v})
    (hF' : A' X F')
    (n : ℕ) :
    IsIsomorphic
      ((Sheaf.functorH (τ'.over X) n).obj F')
      ((Sheaf.functorH (τ.over X) n).obj
        ((comparisonTopologyPullbackAb hle X).obj F')) := sorry

end Degreewise

section Plus

variable (hle : τ' ≤ τ)
variable (P : MorphismProperty C)
variable (A' : ∀ X : C,
  ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
variable [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, HasExt (Sheaf (τ.over X) AddCommGrpCat.{max u v})]
variable [∀ X : C,
  HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
      (τ'.over X) (τ'.over Y))]
variable [∀ X : C, IsGrothendieckAbelian (SiteAbelianSheafCat (τ.over X))]
variable [∀ X : C, IsGrothendieckAbelian (SiteAbelianSheafCat (τ'.over X))]

/-- Lemma 21.30.10 (0EZH) (2): with the all-degree vanishing certificate from 0EZF, bounded-below
selected complexes have the same hypercohomology in every integer degree after the canonical
inverse image. -/
@[stacks 0EZH "(2)"]
theorem hypercohomology_isomorphic_of_plus
    (h : Situation τ τ' P A')
    (hV : Situation.AllVanishing h)
    (X : C)
    (K' : D⁺[A' X])
    (n : ℤ) :
    IsIsomorphic
      ((homologyFunctor AddCommGrpCat.{max u v} n).obj
        ((RΓ[τ'.over X](Over.mk (𝟙 X))).obj
          ((Plus.CohomologyIn.ambient (A' X)).obj K')))
      ((homologyFunctor AddCommGrpCat.{max u v} n).obj
        ((RΓ[τ.over X](Over.mk (𝟙 X))).obj
            ((comparisonTopologyPullbackAb hle X).mapDerivedCategory.obj
            ((Plus.CohomologyIn.ambient (A' X)).obj K')))) := sorry

end Plus

end CategoryTheory.GrothendieckTopology.TopologyComparison.Hypercohomology
