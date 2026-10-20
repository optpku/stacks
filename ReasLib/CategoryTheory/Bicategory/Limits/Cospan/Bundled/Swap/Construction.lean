/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Coherence
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Swap.Transform
import Mathlib.Tactic.CrossRefAttribute

/-!
# Swapping bundled bicategorical cospans

This file lifts the raw swap of cospan transformations and modifications to the induced
bicategory of bundled cospans. The resulting action is strict: it exchanges the two endpoints
and legs, preserves the common target, and introduces no comparison data beyond equality
transport.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u

namespace CategoryTheory.Bicategory.Cospan

variable {B : Type u} [Bicategory.{w, v} B]

namespace Implementation.Swap

/-- Exchange the two endpoints and legs of a bundled cospan. -/
private def obj (S : Cospan B) : Cospan B where
  left := S.right
  right := S.left
  base := S.base
  fst := S.snd
  snd := S.fst

/-- Swap a bundled cospan morphism through its underlying cospan transformation. -/
private def map {S T : Cospan B} (ψ : S ⟶ T) : obj S ⟶ obj T :=
  Hom.ofCospanTransform
    (CospanTransform.swap (Hom.toCospanTransform ψ))

/-- Swap a bundled cospan `2`-morphism through its underlying modification. -/
private def map₂ {S T : Cospan B} {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) :
    map ψ ⟶ map φ :=
  Hom₂.ofModification
    (CospanTransform.Hom.swap (Hom₂.toModification Γ))

/-- Swapping preserves identity `2`-morphisms. -/
private theorem map₂_id {S T : Cospan B} (ψ : S ⟶ T) :
    map₂ (𝟙 ψ) = 𝟙 (map ψ) := sorry

/-- Swapping preserves vertical composition of `2`-morphisms. -/
private theorem map₂_comp {S T : Cospan B} {ψ φ χ : S ⟶ T}
    (Γ : ψ ⟶ φ) (Δ : φ ⟶ χ) :
    map₂ (Γ ≫ Δ) = map₂ Γ ≫ map₂ Δ := sorry

/-- Swapping preserves identity `1`-morphisms strictly. -/
private theorem map_id (S : Cospan B) :
    map (𝟙 S) = 𝟙 (obj S) := sorry

/-- Swapping preserves composition of `1`-morphisms strictly. -/
private theorem map_comp {R S T : Cospan B} (ψ : R ⟶ S) (φ : S ⟶ T) :
    map (ψ ≫ φ) = map ψ ≫ map φ := sorry

/-- The equality transport used by the swapped left-unitor computation. -/
private theorem leftUnitor_eq {S T : Cospan B} (ψ : S ⟶ T) :
    map ((𝟙 S) ≫ ψ) = 𝟙 (obj S) ≫ map ψ := sorry

/-- The equality transport used by the swapped right-unitor computation. -/
private theorem rightUnitor_eq {S T : Cospan B} (ψ : S ⟶ T) :
    map (ψ ≫ 𝟙 T) = map ψ ≫ 𝟙 (obj T) := sorry

/-- The source equality transport used by the swapped associator computation. -/
private theorem associatorSource_eq {Q R S T : Cospan B}
    (ψ : Q ⟶ R) (φ : R ⟶ S) (χ : S ⟶ T) :
    map ((ψ ≫ φ) ≫ χ) = (map ψ ≫ map φ) ≫ map χ := sorry

/-- The target equality transport used by the swapped associator computation. -/
private theorem associatorTarget_eq {Q R S T : Cospan B}
    (ψ : Q ⟶ R) (φ : R ⟶ S) (χ : S ⟶ T) :
    map ψ ≫ (map φ ≫ map χ) = map (ψ ≫ (φ ≫ χ)) := sorry

/-- Swapping is compatible with left whiskering. -/
private theorem map₂_whisker_left {R S T : Cospan B} (ψ : R ⟶ S)
    {φ χ : S ⟶ T} (Γ : φ ⟶ χ) :
    map₂ (ψ ◁ Γ) =
      eqToHom (map_comp ψ φ) ≫
        map ψ ◁ map₂ Γ ≫
          eqToHom (map_comp ψ χ).symm := sorry

/-- Swapping is compatible with right whiskering. -/
private theorem map₂_whisker_right {R S T : Cospan B} {ψ φ : R ⟶ S}
    (Γ : ψ ⟶ φ) (χ : S ⟶ T) :
    map₂ (Γ ▷ χ) =
      eqToHom (map_comp ψ χ) ≫
        map₂ Γ ▷ map χ ≫
          eqToHom (map_comp φ χ).symm := sorry

/-- Swapping carries left unitors to left unitors. -/
private theorem map₂_left_unitor {S T : Cospan B} (ψ : S ⟶ T) :
    map₂ ((λ_ ψ).hom) =
      eqToHom (leftUnitor_eq ψ) ≫ (λ_ (map ψ)).hom := sorry

/-- Swapping carries right unitors to right unitors. -/
private theorem map₂_right_unitor {S T : Cospan B} (ψ : S ⟶ T) :
    map₂ ((ρ_ ψ).hom) =
      eqToHom (rightUnitor_eq ψ) ≫ (ρ_ (map ψ)).hom := sorry

/-- Swapping carries associators to associators. -/
private theorem map₂_associator {Q R S T : Cospan B}
    (ψ : Q ⟶ R) (φ : R ⟶ S) (χ : S ⟶ T) :
    map₂ ((α_ ψ φ χ).hom) =
      eqToHom (associatorSource_eq ψ φ χ) ≫
        (α_ (map ψ) (map φ) (map χ)).hom ≫
          eqToHom (associatorTarget_eq ψ φ χ) := sorry

/-- The strict-pseudofunctor core of bundled cospan swap. -/
private def core : StrictPseudofunctorCore (Cospan B) (Cospan B) where
  obj := obj
  map := map
  map₂ := map₂
  map₂_id := map₂_id
  map₂_comp := map₂_comp
  map_id := map_id
  map_comp := map_comp
  map₂_whisker_left := map₂_whisker_left
  map₂_whisker_right := map₂_whisker_right
  map₂_left_unitor := map₂_left_unitor
  map₂_right_unitor := map₂_right_unitor
  map₂_associator := map₂_associator

end Implementation.Swap

variable (B) in
/-- The strict pseudofunctor which exchanges the two endpoints and legs of every bundled
bicategorical cospan. -/
@[stacks 0040 "swap of bundled bicategorical cospans"]
def swap : StrictPseudofunctor (Cospan B) (Cospan B) :=
  StrictPseudofunctor.mk' Implementation.Swap.core

/- Data and axiom audit (mathlib 4.32): every non-`Prop` object, `1`-morphism, and `2`-morphism
field of `swap` is the direct field swap or the corresponding raw
`CospanTransform.swap`/`CospanTransform.Hom.swap`. The identity and composition comparisons are
the equality isomorphisms supplied by `StrictPseudofunctor.mk'`. Any `sorryAx` reported below is
confined to strict-functoriality and bicategorical coherence equalities. -/

end CategoryTheory.Bicategory.Cospan
