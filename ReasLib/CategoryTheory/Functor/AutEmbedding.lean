/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Algebra.Group.Pi.Basic

@[expose] public section

universe u v w z

namespace CategoryTheory

namespace Functor

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D] (F : C ⥤ D)

/-- Multiplication of natural automorphisms is computed by composing their
objectwise components in reverse order. -/
lemma autEmbedding_map_mul (σ τ : Aut F) :
    (fun X : C ↦ (σ * τ).app X) =
      (fun X : C ↦ (τ.app X).trans (σ.app X)) := sorry

/-- The monoid homomorphism from natural automorphisms of a functor to the
product of its objectwise automorphism groups, given by taking components. -/
def autEmbedding : Aut F →* ∀ X : C, Aut (F.obj X) :=
  MonoidHom.mk' (fun σ X ↦ σ.app X) (autEmbedding_map_mul F)

/-- Evaluating the componentwise automorphism homomorphism at an object gives
the corresponding component of the natural automorphism. -/
lemma autEmbedding_apply (σ : Aut F) (X : C) : autEmbedding F σ X = σ.app X := sorry

/-- A natural automorphism is uniquely determined by its objectwise components. -/
lemma autEmbedding_injective : Function.Injective (autEmbedding F) := sorry

/-- The image of the componentwise automorphism homomorphism consists exactly
of families satisfying the naturality equation for every arrow. -/
lemma autEmbedding_range_eq_compatibility {C : Type u} [Category.{v} C]
    (F : C ⥤ Type w) :
    Set.range (autEmbedding F) =
      ⋂ (f : Arrow C),
        {a | F.map f.hom ≫ (a f.right).hom = (a f.left).hom ≫ F.map f.hom} := sorry

/-- A componentwise automorphism family outside the image of the componentwise
homomorphism fails the naturality equation on some arrow and element. -/
lemma autEmbedding_range_separation {C : Type u} [Category.{v} C]
    (F : C ⥤ Type w)
    (a : ∀ X : C, Aut (F.obj X))
    (ha : a ∉ Set.range (autEmbedding F)) :
    ∃ (f : Arrow C) (x : F.obj f.left),
      F.map f.hom ((a f.left).hom x) ≠ (a f.right).hom (F.map f.hom x) := sorry

end Functor

end CategoryTheory
