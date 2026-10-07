module

public import stacks_project.Chap85.Definition_85_13_1_Pullback
public import stacks_project.Chap85.Definition_85_13_1_System

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
variable [HasAbelianInverseImageFunctoriality J fInv]

/-- Definition 85.13.1 (1)
In Situation 85.3.3, a simplicial system of the derived category, on a family of
component sites `C n` with inverse images `f_φ⁻¹` of abelian sheaves, consists of
objects `K_n` of `D(C_n)` and maps `K_φ : f_φ⁻¹ K_m ⟶ K_n` in `D(C_n)` for
`φ : m ⟶ n`, subject to `K_{φ ∘ ψ} = K_φ ∘ f_φ⁻¹ K_ψ` after the canonical
identification `f_{φ ∘ ψ}⁻¹ = f_φ⁻¹ ∘ f_ψ⁻¹`. -/
@[stacks 0D9G]
abbrev DerivedCategorySystem :=
  DerivedAbelianSystem J fInv

/-- The source-facing system type is the derived abelian system on a family of component
sites. -/
theorem DerivedCategorySystem_eq :
    DerivedCategorySystem J fInv = DerivedAbelianSystem J fInv :=
  sorry

/-- Definition 85.13.1 (2)
In Situation 85.3.3, a simplicial system of the derived category is cartesian if
every `K_φ` is an isomorphism in `D(C_n)`. -/
@[stacks 0D9G]
abbrev DerivedCategorySystem.IsCartesian
    (K : DerivedCategorySystem J fInv) :=
  DerivedAbelianSystem.IsCartesian K

/-- Cartesianness of a derived abelian system is equivalent to every transition being an
isomorphism. -/
theorem DerivedCategorySystem.isCartesian_iff
    (K : DerivedCategorySystem J fInv) :
    DerivedCategorySystem.IsCartesian J fInv K ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (K.map φ) :=
  sorry

/-- Definition 85.13.1 (3)
Given two simplicial systems of the derived category, a morphism is a family
`α_n : K_n ⟶ L_n` in `D(C_n)` natural for the transitions `K_φ`. -/
@[stacks 0D9G]
abbrev DerivedCategorySystem.Hom
    (K L : DerivedCategorySystem J fInv) :=
  DerivedAbelianSystem.Hom K L

/-- A morphism of derived abelian systems is natural for the transitions `K_φ`. -/
theorem DerivedCategorySystem.hom_naturality
    {K L : DerivedCategorySystem J fInv}
    (α : DerivedCategorySystem.Hom J fInv K L)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    K.map φ ≫ α.app n =
      (fInv φ).mapDerivedCategory.map (α.app m) ≫ L.map φ :=
  sorry

end CategoryTheory.SimplicialSites
