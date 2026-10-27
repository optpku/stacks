/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.DerivedSystem
import StacksCheckRecall

/-!
# Definition 85.13.1

In Situation 85.3.3, a simplicial system of the derived category consists of
objects `K_n` of `D(C_n)` and maps `K_φ : f_φ⁻¹ K_m ⟶ K_n` in `D(C_n)` for
`φ : m ⟶ n`, subject to `K_{φ ∘ ψ} = K_φ ∘ f_φ⁻¹ K_ψ` after
`f_{φ ∘ ψ}⁻¹ = f_φ⁻¹ ∘ f_ψ⁻¹`. The system is cartesian when every `K_φ` is an
isomorphism. Morphisms are the obvious stagewise natural maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Functor

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable {C : SimplexCategory → Type u} [∀ n, Category.{v} (C n)]
variable (J : ∀ n, GrothendieckTopology (C n))
variable (fInv : ∀ {m n : SimplexCategory}, (m ⟶ n) →
    Sheaf (J m) AddCommGrpCat.{w} ⥤ Sheaf (J n) AddCommGrpCat.{w})
variable [∀ n, HasSheafify (J n) AddCommGrpCat.{w}]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n), (fInv φ).Additive]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n), PreservesFiniteLimits (fInv φ)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n), PreservesFiniteColimits (fInv φ)]
variable (compIso : ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
    fInv (ψ ≫ φ) ≅ fInv ψ ⋙ fInv φ)

/- Definition 85.13.1 (1)
A simplicial system consists of derived abelian sheaves and inverse-image
transitions compatible with composition. In either case of Situation 85.3.3,
the inverse images and composition comparisons are the canonical ones. -/
@[stacks 0D9G] #check (CategoryTheory.SimplicialSites.DerivedSystem J fInv :
  (∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
    fInv (ψ ≫ φ) ≅ fInv ψ ⋙ fInv φ) → Type (max u v (w + 1)))

/- Definition 85.13.1 (2)
A simplicial system is cartesian exactly when every transition is an isomorphism. -/
@[stacks 0D9G] #check (CategoryTheory.SimplicialSites.DerivedSystem.IsCartesian :
  CategoryTheory.SimplicialSites.DerivedSystem J fInv compIso → Prop)

/- Definition 85.13.1 (3)
Morphisms are stagewise derived-category maps commuting with the transitions. -/
@[stacks 0D9G] #check (CategoryTheory.SimplicialSites.DerivedSystem.Hom :
  CategoryTheory.SimplicialSites.DerivedSystem J fInv compIso →
    CategoryTheory.SimplicialSites.DerivedSystem J fInv compIso → Type (max u v (w + 1)))

end CategoryTheory.SimplicialSites
