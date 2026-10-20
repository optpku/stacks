module

public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Category

public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Sequence.Naturality
public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Sequence.Model.Computation
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Functorial Exact Windows of Cohomological Delta Functors

For a fixed degree, exact windows form a functor on the category of short
exact complexes and vary functorially with the cohomological delta functor.
-/

open CategoryTheory.ComposableArrows

noncomputable section

universe vA uA vB uB

namespace CategoryTheory.CohomologicalDeltaFunctor.exactWindow

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B]

/-- Identity morphisms in the short-exact full subcategory induce identity
maps of exact windows. -/
theorem map_id_hom (F : CohomologicalDeltaFunctor A B) (n : ℕ)
    (S : (ShortComplex.shortExact A).FullSubcategory) :
    map F S.property S.property (InducedCategory.Hom.hom (𝟙 S)) n =
      𝟙 (F.exactWindow S.property n) := sorry

/-- Composition in the short-exact full subcategory is preserved by
exact-window maps. -/
theorem map_comp_hom (F : CohomologicalDeltaFunctor A B) (n : ℕ)
    {S T U : (ShortComplex.shortExact A).FullSubcategory}
    (φ : S ⟶ T) (ψ : T ⟶ U) :
    map F S.property U.property (φ ≫ ψ).hom n =
      map F S.property T.property φ.hom n ≫
        map F T.property U.property ψ.hom n := sorry

/-- For a fixed cohomological delta functor and degree, exact windows are
functorial in short exact complexes. -/
@[stacks 010R "functor of exact windows on short exact complexes"]
noncomputable def functor (F : CohomologicalDeltaFunctor A B) (n : ℕ) :
    (ShortComplex.shortExact A).FullSubcategory ⥤ ComposableArrows B 5 where
  obj S := F.exactWindow S.property n
  map := fun {S T} φ ↦ map F S.property T.property φ.hom n
  map_id := map_id_hom F n
  map_comp := map_comp_hom F n

/-- The object value of the exact-window functor is the pointwise exact
window. -/
@[simp]
theorem functor_obj (F : CohomologicalDeltaFunctor A B) (n : ℕ)
    (S : (ShortComplex.shortExact A).FullSubcategory) :
    (functor F n).obj S = F.exactWindow S.property n := sorry

/-- The map of the exact-window functor is the pointwise naturality map. -/
@[simp]
theorem functor_map (F : CohomologicalDeltaFunctor A B) (n : ℕ)
    {S T : (ShortComplex.shortExact A).FullSubcategory} (f : S ⟶ T) :
    (functor F n).map f = map F S.property T.property f.hom n := sorry

/-- Pointwise maps of exact windows are natural in the short exact complex. -/
@[stacks 010R "naturality of maps between exact-window functors"]
theorem natTrans_naturality {F G : CohomologicalDeltaFunctor A B} (τ : F ⟶ G)
    (n : ℕ) {S T : (ShortComplex.shortExact A).FullSubcategory} (f : S ⟶ T) :
    (functor F n).map f ≫ exactWindowMap τ T.property n =
      exactWindowMap τ S.property n ≫ (functor G n).map f := sorry

/-- A morphism of cohomological delta functors induces a natural
transformation between their exact-window functors. -/
@[stacks 010R "natural transformation of exact-window functors"]
noncomputable def natTrans {F G : CohomologicalDeltaFunctor A B} (τ : F ⟶ G)
    (n : ℕ) : functor F n ⟶ functor G n where
  app S := exactWindowMap τ S.property n
  naturality := fun {_ _} f ↦ natTrans_naturality τ n f

/-- The component of `natTrans` is the pointwise map of exact windows. -/
@[simp]
theorem natTrans_app {F G : CohomologicalDeltaFunctor A B} (τ : F ⟶ G)
    (n : ℕ) (S : (ShortComplex.shortExact A).FullSubcategory) :
    (natTrans τ n).app S = exactWindowMap τ S.property n := sorry

/-- The exact-window natural transformation of an identity morphism is the
identity. -/
@[simp]
theorem natTrans_id (F : CohomologicalDeltaFunctor A B) (n : ℕ) :
    natTrans (𝟙 F) n = 𝟙 (functor F n) := sorry

/-- Exact-window natural transformations preserve composition. -/
@[simp]
theorem natTrans_comp {F G H : CohomologicalDeltaFunctor A B}
    (τ : F ⟶ G) (σ : G ⟶ H) (n : ℕ) :
    natTrans (τ ≫ σ) n = natTrans τ n ≫ natTrans σ n := sorry

/-- In degree `n`, taking the exact-window functor is itself functorial in
the cohomological delta functor. -/
@[stacks 010R "exact-window functor of cohomological delta functors"]
noncomputable def modelFunctor (n : ℕ) :
    CohomologicalDeltaFunctor A B ⥤
      ((ShortComplex.shortExact A).FullSubcategory ⥤ ComposableArrows B 5) where
  obj F := functor F n
  map τ := natTrans τ n
  map_id := fun F ↦ natTrans_id F n
  map_comp := fun τ σ ↦ natTrans_comp τ σ n

/-- Evaluating `modelFunctor` at a delta functor gives its exact-window
functor. -/
@[simp]
theorem modelFunctor_obj (F : CohomologicalDeltaFunctor A B) (n : ℕ) :
    (modelFunctor (A := A) (B := B) n).obj F = functor F n := sorry

/-- Evaluating the map of `modelFunctor` gives the pointwise exact-window
map. -/
@[simp]
theorem modelFunctor_map_app {F G : CohomologicalDeltaFunctor A B}
    (τ : F ⟶ G) (n : ℕ) (S : (ShortComplex.shortExact A).FullSubcategory) :
    ((modelFunctor (A := A) (B := B) n).map τ).app S =
      exactWindowMap τ S.property n := sorry

/-- The low-degree exact-window functor of a cohomological delta functor. -/
abbrev lowDegreeFunctor (F : CohomologicalDeltaFunctor A B) :
    (ShortComplex.shortExact A).FullSubcategory ⥤ ComposableArrows B 5 :=
  functor F 0

/-- Low-degree exact windows vary functorially with the cohomological delta
functor. -/
abbrev lowDegreeModelFunctor :
    CohomologicalDeltaFunctor A B ⥤
      ((ShortComplex.shortExact A).FullSubcategory ⥤ ComposableArrows B 5) :=
  modelFunctor 0

end CategoryTheory.CohomologicalDeltaFunctor.exactWindow
