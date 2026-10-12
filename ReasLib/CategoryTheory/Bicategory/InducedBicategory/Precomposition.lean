/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.LocalProperties

/-!
# Precomposition from induced hom-categories to the ambient bicategory

An induced bicategory has the same `1`- and `2`-morphisms as its ambient
bicategory. This module packages the recurring operation that first forgets an
induced morphism and then precomposes it by an ambient morphism.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory
open scoped Bicategory

universe w v u u'

namespace Bicategory.InducedBicategory

variable {B : Type u'} {D : Type u} [Bicategory.{w, v} D] {F : B → D}

/-- Precomposition from an induced hom-category to an ambient hom-category. The source of `i`
need not lie in the induced bicategory; only its target is required to be the ambient object
underlying `Y`. -/
noncomputable abbrev precompToAmbient
    (Z : InducedBicategory D F) {X : D} {Y : InducedBicategory D F}
    (i : X ⟶ F Y) :
    (Y ⟶ Z) ⥤ (X ⟶ F Z) :=
  (homEquivalence Y Z).inverse ⋙ Bicategory.precomp (F Z) i

/-- On objects, induced-to-ambient precomposition forgets the induced morphism and composes it
with the given ambient morphism. -/
@[simp]
theorem precompToAmbient.obj
    (Z : InducedBicategory D F) {X : D} {Y : InducedBicategory D F}
    (i : X ⟶ F Y) (G : Y ⟶ Z) :
    (precompToAmbient Z i).obj G = i ≫ G.hom := sorry

/-- On morphisms, induced-to-ambient precomposition is left whiskering of the underlying
ambient `2`-morphism. -/
@[simp]
theorem precompToAmbient.map
    (Z : InducedBicategory D F) {X : D} {Y : InducedBicategory D F}
    (i : X ⟶ F Y) {G H : Y ⟶ Z} (η : G ⟶ H) :
    (precompToAmbient Z i).map η = i ◁ η.hom := sorry

/-- The induced-to-ambient precomposition functor is an equivalence whenever ambient
precomposition by the same morphism is an equivalence. -/
theorem precompToAmbient.isEquivalence
    (Z : InducedBicategory D F) {X : D} {Y : InducedBicategory D F}
    (i : X ⟶ F Y)
    (hprecomp : (Bicategory.precomp (F Z) i).IsEquivalence) :
    (precompToAmbient Z i).IsEquivalence := sorry

end Bicategory.InducedBicategory

end CategoryTheory
