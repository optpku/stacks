/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import stacks_project.Chap85.Lemma_85_15_1
public import stacks_project.Chap85.Lemma_85_3_2_Total

/-!
# Simplicial site of a simplicial semi-representable object

A simplicial object `K` of `SR(C)` induces the simplicial object of sites
`n ↦ OverSite (K.obj n)`, with structure maps `overMap (K.map φ)` and stage
coverings `(overTopology J (K.obj n)).toPrecoverage`.
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits
open scoped SemiRepresentableFamily Simplicial

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]

/-- The functor sending a semi-representable object to its localization site, as an object of
`Cat`. -/
def overSiteFunctor : FormalCoproduct.{w} C ⥤ Cat.{max u v w, max u v w} where
  obj K := Cat.of (OverSite K)
  map φ := (overMap φ).toCatHom
  map_id := sorry
  map_comp := sorry

/-- The object action of `overSiteFunctor` is `Cat.of (OverSite K)`. -/
theorem overSiteFunctor_obj (K : FormalCoproduct.{w} C) :
    overSiteFunctor.obj K = Cat.of (OverSite K) :=
  sorry

/-- The morphism action of `overSiteFunctor` is `overMap`. -/
theorem overSiteFunctor_map {K L : FormalCoproduct.{w} C} (φ : K ⟶ L) :
    overSiteFunctor.map φ = (overMap φ).toCatHom :=
  sorry

/-- The simplicial object of sites `n ↦ C / K_n` associated to a simplicial object of `SR(C)`. -/
def overSiteDiagram (K : SimplicialObject (FormalCoproduct.{w} C)) :
    SimplicialObject Cat.{max u v w, max u v w} :=
  K ⋙ overSiteFunctor

/-- The stage category of `overSiteDiagram K` at `n` is `OverSite (K.obj n)`. -/
theorem overSiteDiagram_obj (K : SimplicialObject (FormalCoproduct.{w} C))
    (n : SimplexCategoryᵒᵖ) :
    (overSiteDiagram K).obj n = Cat.of (OverSite (K.obj n)) :=
  sorry

/-- Structure maps of `overSiteDiagram K` are relocalization `overMap (K.map φ)`. -/
theorem overSiteDiagram_map (K : SimplicialObject (FormalCoproduct.{w} C))
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    (overSiteDiagram K).map φ = (overMap (K.map φ)).toCatHom :=
  sorry

variable (J : GrothendieckTopology C)

/-- The stage precoverage on `OverSite (K.obj n)` induced by `J`. -/
def overSitePrecoverage (K : SimplicialObject (FormalCoproduct.{w} C))
    (n : SimplexCategoryᵒᵖ) :
    Precoverage ((overSiteDiagram K).obj n) :=
  (overTopology J (K.obj n)).toPrecoverage

/-- A presieve covers in `overSitePrecoverage J K n` iff the generated sieve covers for
`overTopology J (K.obj n)`. -/
theorem mem_overSitePrecoverage_iff (K : SimplicialObject (FormalCoproduct.{w} C))
    {n : SimplexCategoryᵒᵖ} {V : OverSite (K.obj n)} {R : Presieve V} :
    R ∈ overSitePrecoverage J K n V ↔
      Sieve.generate R ∈ overTopology J (K.obj n) V :=
  sorry

/-- If `K` is a simplicial object of `SR(C)`, then `n ↦ C / K_n` is a fiberwise simplicial
site: each stage is a site and each `overMap (K.map φ)` has property `P`. -/
instance overSiteDiagram_isFiberwiseSite (K : SimplicialObject (FormalCoproduct.{w} C)) :
    Grothendieck.IsFiberwiseSite (overSiteDiagram K) (overSitePrecoverage J K) :=
  sorry

end CategoryTheory.SemiRepresentableFamily
