/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Evaluation.At.Basic

/-!
# Source-morphism action on point evaluation

Strong transformations and modifications induced by source 1- and 2-morphisms,
together with the resulting functor on source hom-categories. Computation rules
live in `Evaluation.Action.Computations`.
-/

@[expose] public section

universe wB vB uB wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {B : Type uB} [Bicategory.{wB, vB} B]
  {D : Type uD} [Bicategory.{wD, vD} D]

section Evaluation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- Naturality in modifications for the strong transformation induced by a source
`1`-morphism. -/
private theorem evaluationMap_naturality_naturality
    {a b : B} (f : a ⟶ b) {F G : Pseudofunctor B D}
    {η θ : F ⟶ G} (Γ : η ⟶ θ) :
    Γ.as.app a ▷ G.map f ≫ (θ.naturality f).inv =
      (η.naturality f).inv ≫ F.map f ◁ Γ.as.app b := sorry

/-- Identity coherence for the strong transformation induced by a source `1`-morphism. -/
private theorem evaluationMap_naturality_id
    {a b : B} (f : a ⟶ b) (F : Pseudofunctor B D) :
    ((𝟙 F : F ⟶ F).naturality f).inv ≫
        F.map f ◁ ((evaluationAt D b).mapId F).hom =
      ((evaluationAt D a).mapId F).hom ▷ F.map f ≫
        (λ_ (F.map f)).hom ≫ (ρ_ (F.map f)).inv := sorry

/-- Composition coherence for the strong transformation induced by a source `1`-morphism. -/
private theorem evaluationMap_naturality_comp
    {a b : B} (f : a ⟶ b) {F G H : Pseudofunctor B D}
    (η : F ⟶ G) (θ : G ⟶ H) :
    ((η ≫ θ).naturality f).inv ≫
        F.map f ◁ ((evaluationAt D b).mapComp η θ).hom =
      ((evaluationAt D a).mapComp η θ).hom ▷ H.map f ≫
        (α_ (η.app a) (θ.app a) (H.map f)).hom ≫
        η.app a ◁ (θ.naturality f).inv ≫
        (α_ (η.app a) (G.map f) (θ.app b)).inv ≫
        (η.naturality f).inv ▷ θ.app b ≫
        (α_ (F.map f) (η.app b) (θ.app b)).hom := sorry

variable (D) in
/-- A `1`-morphism of the source induces a strong transformation between the corresponding
point-evaluation pseudofunctors. Its naturality is the inverse of strong-transformation
naturality in the functor bicategory. -/
def evaluationMap {a b : B} (f : a ⟶ b) :
    (evaluationAt D a).toPseudofunctor ⟶
      (evaluationAt D b).toPseudofunctor where
  app F := F.map f
  naturality η := (η.naturality f).symm
  naturality_naturality := evaluationMap_naturality_naturality f
  naturality_id := evaluationMap_naturality_id f
  naturality_comp := evaluationMap_naturality_comp f

/-- Naturality of the modification obtained by evaluating a source `2`-morphism. -/
private theorem evaluationMap₂_naturality
    {a b : B} {f g : a ⟶ b} (γ : f ⟶ g)
    {F G : Pseudofunctor B D} (η : F ⟶ G) :
    η.app a ◁ G.map₂ γ ≫ (η.naturality g).inv =
      (η.naturality f).inv ≫ F.map₂ γ ▷ η.app b := sorry

variable (D) in
/-- A `2`-morphism of the source induces a modification between the corresponding
evaluation transformations. -/
def evaluationMap₂
    {a b : B} {f g : a ⟶ b} (γ : f ⟶ g) :
    evaluationMap D f ⟶ evaluationMap D g where
  as.app F := F.map₂ γ
  as.naturality := evaluationMap₂_naturality γ

/-- Evaluation of source `2`-morphisms preserves identities. -/
@[simp]
theorem evaluationMap₂.id
    {a b : B} (f : a ⟶ b) :
    evaluationMap₂ D (𝟙 f) = 𝟙 (evaluationMap D f) := sorry

/-- Evaluation of source `2`-morphisms preserves vertical composition. -/
@[simp]
theorem evaluationMap₂.comp
    {a b : B} {f g h : a ⟶ b} (γ : f ⟶ g) (δ : g ⟶ h) :
    evaluationMap₂ D (γ ≫ δ) =
      evaluationMap₂ D γ ≫ evaluationMap₂ D δ := sorry

variable (D) in
/-- Evaluation on the hom-category of the source. This functor sends `1`-morphisms to
evaluation strong transformations and `2`-morphisms to evaluation modifications. -/
def evaluationMapFunctor (a b : B) :
    (a ⟶ b) ⥤
      ((evaluationAt D a).toPseudofunctor ⟶
        (evaluationAt D b).toPseudofunctor) where
  obj := evaluationMap D
  map := evaluationMap₂ D
  map_id := evaluationMap₂.id (D := D)
  map_comp := evaluationMap₂.comp (D := D)

end Evaluation

end Pseudofunctor

end CategoryTheory
