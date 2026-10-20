/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import ReasLib.CategoryTheory.Sites.Family.Localization
public import ReasLib.CategoryTheory.Sites.Grothendieck.SimplicialTopos

/-!
# Simplicial site of a simplicial semi-representable object

A simplicial object `K` of `SR(C)` induces the simplicial object of sites
`n ↦ OverSite (K.obj n)`, with structure maps `overMap (K.map φ)` and stage
coverings `(overTopology J (K.obj n)).toPrecoverage`.
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]

/-- Relocalization along an identity family morphism is the identity functor. -/
theorem overSiteFunctor_map_id (K : FormalCoproduct.{w} C) :
    (overMap (𝟙 K)).toCatHom = 𝟙 (Cat.of (OverSite K)) :=
  sorry

/-- Relocalization along a composite is the composite of the relocalizations. -/
theorem overSiteFunctor_map_comp {K L M : FormalCoproduct.{w} C}
    (φ : K ⟶ L) (ψ : L ⟶ M) :
    (overMap (φ ≫ ψ)).toCatHom = (overMap φ).toCatHom ≫ (overMap ψ).toCatHom :=
  sorry

/-- The functor sending a semi-representable object to its localization site, as an object of
`Cat`. -/
def overSiteFunctor : FormalCoproduct.{w} C ⥤ Cat.{max u v w, max u v w} where
  obj K := Cat.of (OverSite K)
  map φ := (overMap φ).toCatHom
  map_id := overSiteFunctor_map_id
  map_comp := overSiteFunctor_map_comp

/-- The object action of `overSiteFunctor` is `Cat.of (OverSite K)`. -/
theorem overSiteFunctor_obj (K : FormalCoproduct.{w} C) :
    overSiteFunctor.obj K = Cat.of (OverSite K) :=
  rfl

/-- The morphism action of `overSiteFunctor` is `overMap`. -/
theorem overSiteFunctor_map {K L : FormalCoproduct.{w} C} (φ : K ⟶ L) :
    overSiteFunctor.map φ = (overMap φ).toCatHom :=
  rfl

/-- The simplicial object of sites `n ↦ C / K_n` associated to a simplicial object of `SR(C)`. -/
def overSiteDiagram (K : SimplicialObject (FormalCoproduct.{w} C)) :
    SimplicialObject Cat.{max u v w, max u v w} :=
  K ⋙ overSiteFunctor

/-- The stage category of `overSiteDiagram K` at `n` is `OverSite (K.obj n)`. -/
theorem overSiteDiagram_obj (K : SimplicialObject (FormalCoproduct.{w} C))
    (n : SimplexCategoryᵒᵖ) :
    (overSiteDiagram K).obj n = Cat.of (OverSite (K.obj n)) :=
  rfl

/-- Structure maps of `overSiteDiagram K` are relocalization `overMap (K.map φ)`. -/
theorem overSiteDiagram_map (K : SimplicialObject (FormalCoproduct.{w} C))
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    (overSiteDiagram K).map φ = (overMap (K.map φ)).toCatHom :=
  rfl

variable (J : GrothendieckTopology C)

/-- The saturated stage precoverage presenting the localization Grothendieck
topology. Its covering arrows need not all admit pullbacks; the selected-cover
site presentation is `overSiteSelectedPrecoverage`. -/
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

/-- The selected covering families on the stage localization of a simplicial
semi-representable object. -/
def overSiteSelectedPrecoverage (P : Precoverage C)
    (K : SimplicialObject (FormalCoproduct.{w} C)) (n : SimplexCategoryᵒᵖ) :
    Precoverage ((overSiteDiagram K).obj n) :=
  localizationPrecoverage P (K.obj n)

/-- Each selected localization stage generates the original localization topology. -/
theorem overSiteSelectedPrecoverage_toGrothendieck (P : Precoverage C) [P.IsSite]
    (K : SimplicialObject (FormalCoproduct.{w} C)) (n : SimplexCategoryᵒᵖ) :
    (overSiteSelectedPrecoverage P K n).toGrothendieck =
      overTopology P.toGrothendieck (K.obj n) :=
  localizationPrecoverage_toGrothendieck P (K.obj n)

/-- The simplicial localization is a fiberwise site for the original selected
covering families, with property P supplied by relocalization. -/
instance overSiteDiagram_isFiberwiseSite (P : Precoverage C) [P.IsSite]
    (K : SimplicialObject (FormalCoproduct.{w} C)) :
    Grothendieck.IsFiberwiseSite (overSiteDiagram K) (overSiteSelectedPrecoverage P K) where
  isSite n := localizationPrecoverage_isSite P (K.obj n)
  hasCoverLifts φ := overMap_hasCoverLifts P (K.map φ)

/-- Saturated localization topologies have the continuity properties for sheaf
comparisons. This does not assert the stronger selected-cover pullback axioms. -/
instance overSiteDiagram_hasSheafTransitions (K : SimplicialObject (FormalCoproduct.{w} C)) :
    Grothendieck.HasSheafTransitions (overSiteDiagram K) (overSitePrecoverage J K) :=
  sorry

/-- Generating the total topology from selected localization covers gives the
same topology as generating it from their saturated stage presentations. -/
theorem overSiteSelectedPrecoverage_totalTopology (P : Precoverage C) [P.IsSite]
    (K : SimplicialObject (FormalCoproduct.{w} C)) :
    Grothendieck.topology (overSiteDiagram K) (overSiteSelectedPrecoverage P K) =
      Grothendieck.topology (overSiteDiagram K) (overSitePrecoverage P.toGrothendieck K) :=
  sorry

end CategoryTheory.SemiRepresentableFamily
