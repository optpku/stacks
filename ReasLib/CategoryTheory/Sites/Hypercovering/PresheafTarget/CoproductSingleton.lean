/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Singleton.Presheaf
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Singleton.Simplicial
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Terminal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Singleton-coproduct replacements of site-level hypercoverings

This leaf transfers the hypercovering conditions across a degreewise replacement of a
semi-representable family by the singleton family on its coproduct.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory

open Limits
open scoped CategoryTheory.SemiRepresentableFamily

namespace HypercoveringOf.Terminal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type (max w v))]

namespace CoproductSingleton

/-- The canonical simplicial singleton-coproduct replacement underlying a site-level
hypercovering. -/
abbrev simplicial
    (K : HypercoveringOf.Terminal.{w} J)
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (K.simplicial.obj Δ).obj] :
    SimplicialObject (SR(C)) :=
  FormalCoproduct.Simplicial.coproductSingleton K.simplicial

/-- The degreewise presheaf comparison from a hypercovering to its canonical simplicial
singleton-coproduct replacement. -/
def comparison
    (K : HypercoveringOf.Terminal.{w} J)
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (K.simplicial.obj Δ).obj]
    (Δ : SimplexCategoryᵒᵖ) :
    FormalCoproduct.toPresheaf.obj (K.simplicial.obj Δ) ⟶
      FormalCoproduct.toPresheaf.obj ((simplicial K).obj Δ) :=
  FormalCoproduct.coproductSingletonComparison
    (K.simplicial.obj Δ) ((simplicial K).obj Δ) rfl

/-- The degreewise comparison is induced by the corresponding component of the canonical
simplicial morphism to the singleton-coproduct replacement. -/
@[simp] theorem comparison_def
    (K : HypercoveringOf.Terminal.{w} J)
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (K.simplicial.obj Δ).obj]
    (Δ : SimplexCategoryᵒᵖ) :
    comparison K Δ =
      FormalCoproduct.toPresheaf.map
        ((FormalCoproduct.Simplicial.toCoproductSingleton K.simplicial).app Δ) := sorry

/-- Degree-zero local surjectivity transfers across a degreewise singleton-coproduct replacement
whose comparison maps become isomorphisms after sheafification. -/
theorem zeroLocallySurjective
    (K : HypercoveringOf.Terminal.{w} J)
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (K.simplicial.obj Δ).obj]
    [∀ Δ : SimplexCategoryᵒᵖ,
      IsIso ((presheafToSheaf J (Type (max w v))).map (comparison K Δ))] :
    ZeroLocallySurjective J (simplicial K) := sorry

/-- Degree-one local surjectivity transfers across a degreewise singleton-coproduct replacement
whose comparison maps become isomorphisms after sheafification. -/
theorem oneLocallySurjective
    (K : HypercoveringOf.Terminal.{w} J)
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (K.simplicial.obj Δ).obj]
    [∀ Δ : SimplexCategoryᵒᵖ,
      IsIso ((presheafToSheaf J (Type (max w v))).map (comparison K Δ))] :
    OneLocallySurjective J (simplicial K) := sorry

/-- Every higher local-surjectivity condition transfers across a degreewise
singleton-coproduct replacement whose comparison maps become isomorphisms after
sheafification. -/
theorem higherLocallySurjective
    (K : HypercoveringOf.Terminal.{w} J)
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (K.simplicial.obj Δ).obj]
    [∀ Δ : SimplexCategoryᵒᵖ,
      IsIso ((presheafToSheaf J (Type (max w v))).map (comparison K Δ))]
    (n : ℕ) :
    HigherLocallySurjective J (simplicial K) (n + 1) := sorry

end CoproductSingleton

/-- Remark 25.12.8 (0DB1): replace every degree of a site-level hypercovering by the singleton
family on its coproduct, provided the induced comparison maps become isomorphisms after
sheafification. -/
@[stacks 0DB1 "singleton-coproduct replacement of a site-level hypercovering"]
def coproductSingleton
    (K : HypercoveringOf.Terminal.{w} J)
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (K.simplicial.obj Δ).obj]
    [∀ Δ : SimplexCategoryᵒᵖ,
      IsIso ((presheafToSheaf J (Type (max w v))).map
        (CoproductSingleton.comparison K Δ))] :
    HypercoveringOf.Terminal.{w} J :=
  ofSimplicial J (CoproductSingleton.simplicial K)
    (CoproductSingleton.zeroLocallySurjective K)
    (CoproductSingleton.oneLocallySurjective K)
    (fun n ↦ CoproductSingleton.higherLocallySurjective K n)

/-- The underlying simplicial object of `coproductSingleton` is the canonical degreewise
singleton-coproduct replacement. -/
@[simp] theorem coproductSingleton_simplicial
    (K : HypercoveringOf.Terminal.{w} J)
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (K.simplicial.obj Δ).obj]
    [∀ Δ : SimplexCategoryᵒᵖ,
      IsIso ((presheafToSheaf J (Type (max w v))).map
        (CoproductSingleton.comparison K Δ))] :
    (coproductSingleton K).simplicial = CoproductSingleton.simplicial K := sorry

end HypercoveringOf.Terminal
end CategoryTheory
