/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Map

/-!
# Diagonal square of a categorical pullback

This module constructs the canonical diagonal functor, the cospan actions induced by
postcomposition and diagonalization, and the resulting comparison functor between categorical
pullbacks. The explicit inverse and equivalence data live in
`CategoricalPullback.Diagonal.Equivalence`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

namespace CategoryTheory.Limits

open Functor

universe v₁ v₂ u₁ u₂

variable {C₀ : Type u₁} [Category.{v₁} C₀]
variable {D₀ : Type u₂} [Category.{v₂} D₀]

namespace CategoricalPullback

/- `diagonal` is an ordinary data owner. Its components still compute when explicitly unfolded,
but the public API does not force global transparency merely to support the mathematical notation
`Δₚ`. -/

/-- The canonical diagonal functor `Δₚ H : C₀ ⥤ H ⊡ H` attached to `H : C₀ ⥤ D₀`:

It sends an object of `C₀` to the pair consisting of that object twice, together with the
identity comparison in the self-pullback `H ⊡ H`. -/
def diagonal (H : C₀ ⥤ D₀) : C₀ ⥤ H ⊡ H :=
  (toFunctorToCategoricalPullback H H C₀).obj
    { fst := 𝟭 C₀
      snd := 𝟭 C₀
      iso := Iso.refl _ }

end CategoricalPullback

/- `Δₚ` is public notation for the relative diagonal and is used repeatedly by the comparison
API below. -/
end CategoryTheory.Limits

@[inherit_doc CategoryTheory.Limits.CategoricalPullback.diagonal]
scoped[CategoricalPullback] notation "Δₚ" =>
  CategoryTheory.Limits.CategoricalPullback.diagonal

namespace CategoryTheory.Limits

open Functor

universe vA vB vC vD uA uB uC uD

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]
variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

namespace CategoricalPullback

/- The projection and cospan-action constructions below are ordinary data owners, not transparent
aliases. Their component behavior is exposed by named simp lemmas where it matters to statements;
the explicit inverse may unfold them internally without imposing `abbrev` semantics downstream. -/

/-- The functor from `F ⊡ G` to the base category `C`, obtained from the first projection. -/
def toBase (F : A ⥤ C) (G : B ⥤ C) : F ⊡ G ⥤ C :=
  π₁ F G ⋙ F

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace postcompose

/-- The cospan transformation that postcomposes both legs by `H`:

```
                  F                           G
       A ─────────────────▶ C ◀────────────────── B
       │                    │                     │
   𝟭 A │                  H │                 𝟭 B │
       ▼                    ▼                     ▼
       A ─────────────────▶ D ◀────────────────── B
                F ⋙ H                       G ⋙ H
``` -/
def transform
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    CatCospanTransform F G (F ⋙ H) (G ⋙ H) :=
  CatCospanTransform.ofIso
    (leftUnitor (F ⋙ H)).symm
    (leftUnitor (G ⋙ H)).symm

end postcompose

/-- Postcomposing the pullback structural isomorphism by `H` induces the canonical
functor between the two categorical pullbacks.

It maps the pullback of `F` and `G` to the pullback obtained after postcomposing both legs
with `H`.

This is the canonical action of postcomposition on categorical pullbacks. -/
def postcompose (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    F ⊡ G ⥤ (F ⋙ H) ⊡ (G ⋙ H) :=
  map (postcompose.transform F G H)

/-- Postcomposition commutes with the left pullback projection. -/
def postcomposeFstIso (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    postcompose F G H ⋙ π₁ (F ⋙ H) (G ⋙ H) ≅ π₁ F G :=
  mapFstIso (postcompose.transform F G H) ≪≫ rightUnitor _

/-- Postcomposition commutes with the right pullback projection. -/
def postcomposeSndIso (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    postcompose F G H ⋙ π₂ (F ⋙ H) (G ⋙ H) ≅ π₂ F G :=
  mapSndIso (postcompose.transform F G H) ≪≫ rightUnitor _

namespace Implementation

/-- The cospan transformation from the postcomposed cospan to the diagonal cospan on `H`:

```
                F ⋙ H                       G ⋙ H
       A ─────────────────▶ D ◀────────────────── B
       │                    │                     │
     F │                𝟭 D │                   G │
       ▼                    ▼                     ▼
       C ─────────────────▶ D ◀────────────────── C
                  H                           H
``` -/
private def toDiagonalTransform
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    CatCospanTransform (F ⋙ H) (G ⋙ H) H H :=
  CatCospanTransform.ofIso
    (rightUnitor (F ⋙ H))
    (rightUnitor (G ⋙ H))

end Implementation

/-- The induced functor from the postcomposed pullback to the diagonal pullback:

It maps the pullback of the postcomposed legs to the diagonal self-pullback `H ⊡ H`.

This is the canonical cospan action on categorical pullbacks. -/
def toDiagonal (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    (F ⋙ H) ⊡ (G ⋙ H) ⥤ H ⊡ H :=
  map (Implementation.toDiagonalTransform F G H)

/-- Mapping to the diagonal self-pullback commutes with the left projection. -/
def toDiagonalFstIso (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    toDiagonal F G H ⋙ π₁ H H ≅ π₁ (F ⋙ H) (G ⋙ H) ⋙ F :=
  mapFstIso (Implementation.toDiagonalTransform F G H)

/-- Mapping to the diagonal self-pullback commutes with the right projection. -/
def toDiagonalSndIso (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    toDiagonal F G H ⋙ π₂ H H ≅ π₂ (F ⋙ H) (G ⋙ H) ⋙ G :=
  mapSndIso (Implementation.toDiagonalTransform F G H)

end CategoricalPullback

end CategoryTheory.Limits
