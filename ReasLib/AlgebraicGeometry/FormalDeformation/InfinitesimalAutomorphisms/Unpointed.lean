module

public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Predeformation
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Map

/-!
# Unpointed infinitesimal vector spaces

Infinitesimal automorphisms of a predeformation category satisfying the
Rim-Schlessinger condition form a vector space, functorial in based functors.
-/

@[expose] public section

noncomputable section

open CategoryTheory ArtinianLocalAlgCat Functor BasedCategory
open scoped Bicategory BasedFunctor
open Fiber
open Functor.Chosen

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {E : Type v} [Category.{w} E]
variable {p : E ⥤ ArtinianLocalAlgCat Λ k}

namespace CategoryTheory.Functor

/-- Addition on unpointed `Inf(p)` agrees with composition of automorphisms. -/
instance instAdd_infinitesimalAutomorphisms [IsPredeformationCategory p] :
    Add (infinitesimalAutomorphisms p) where
  add α β := α * β

/-- The identity automorphism is the zero of unpointed `Inf(p)`. -/
instance instZero_infinitesimalAutomorphisms [IsPredeformationCategory p] :
    Zero (infinitesimalAutomorphisms p) where
  zero := 1

/-- Negation on unpointed `Inf(p)` is inversion of automorphisms. -/
instance instNeg_infinitesimalAutomorphisms [IsPredeformationCategory p] :
    Neg (infinitesimalAutomorphisms p) where
  neg α := α⁻¹

/-- Scalar multiplication on unpointed `Inf(p)`, transported from `infinitesimalAutomorphismsAt`
along `infinitesimalAutomorphismsEquivAt` at the chosen dual-number pushforward. -/
instance instSMul_infinitesimalAutomorphisms [IsPredeformationCategory p]
    [HasRimSchlessinger p] : SMul k (infinitesimalAutomorphisms p) where
  smul r α :=
    (infinitesimalAutomorphismsEquivAt p (chosenResidueFiberObj p)
          (pushforwardObj p (residueToDualNumber Λ k) (chosenResidueFiberObj p))
          (chosenDualNumberHom p (chosenResidueFiberObj p))).symm
      (r • infinitesimalAutomorphismsEquivAt p (chosenResidueFiberObj p)
          (pushforwardObj p (residueToDualNumber Λ k) (chosenResidueFiberObj p))
          (chosenDualNumberHom p (chosenResidueFiberObj p)) α)

/-- Composition, the identity, and inversion on unpointed infinitesimal automorphisms
satisfy the commutative additive group laws. -/
theorem infinitesimalAutomorphisms_addCommGroup_laws [IsPredeformationCategory p]
    [HasRimSchlessinger p] :
    (∀ α β γ : infinitesimalAutomorphisms p, (α + β) + γ = α + (β + γ)) ∧
    (∀ α : infinitesimalAutomorphisms p, 0 + α = α) ∧
    (∀ α : infinitesimalAutomorphisms p, α + 0 = α) ∧
    (∀ α : infinitesimalAutomorphisms p, -α + α = 0) ∧
    (∀ α β : infinitesimalAutomorphisms p, α + β = β + α) := sorry

/-- Unpointed infinitesimal automorphisms form an additive commutative group. -/
instance instAddCommGroup_infinitesimalAutomorphisms [IsPredeformationCategory p]
    [HasRimSchlessinger p] : AddCommGroup (infinitesimalAutomorphisms p) where
  add_assoc := (infinitesimalAutomorphisms_addCommGroup_laws (p := p)).1
  zero_add := (infinitesimalAutomorphisms_addCommGroup_laws (p := p)).2.1
  add_zero := (infinitesimalAutomorphisms_addCommGroup_laws (p := p)).2.2.1
  nsmul := nsmulRec
  neg_add_cancel := (infinitesimalAutomorphisms_addCommGroup_laws (p := p)).2.2.2.1
  zsmul := zsmulRec
  add_comm := (infinitesimalAutomorphisms_addCommGroup_laws (p := p)).2.2.2.2

/-- The scalar action transported from pointed infinitesimal automorphisms satisfies
the module laws for composition-defined addition. -/
theorem infinitesimalAutomorphisms_module_laws [IsPredeformationCategory p]
    [HasRimSchlessinger p] :
    (∀ α : infinitesimalAutomorphisms p, (1 : k) • α = α) ∧
    (∀ r s : k, ∀ α : infinitesimalAutomorphisms p, (r * s) • α = r • s • α) ∧
    (∀ r : k, r • (0 : infinitesimalAutomorphisms p) = 0) ∧
    (∀ r : k, ∀ α β : infinitesimalAutomorphisms p, r • (α + β) = r • α + r • β) ∧
    (∀ r s : k, ∀ α : infinitesimalAutomorphisms p, (r + s) • α = r • α + s • α) ∧
    (∀ α : infinitesimalAutomorphisms p, (0 : k) • α = 0) := sorry

/-- Unpointed infinitesimal automorphisms carry the transported vector-space structure. -/
instance instModule_infinitesimalAutomorphisms [IsPredeformationCategory p]
    [HasRimSchlessinger p] : Module k (infinitesimalAutomorphisms p) where
  one_smul := (infinitesimalAutomorphisms_module_laws (p := p)).1
  mul_smul := (infinitesimalAutomorphisms_module_laws (p := p)).2.1
  smul_zero := (infinitesimalAutomorphisms_module_laws (p := p)).2.2.1
  smul_add := (infinitesimalAutomorphisms_module_laws (p := p)).2.2.2.1
  add_smul := (infinitesimalAutomorphisms_module_laws (p := p)).2.2.2.2.1
  zero_smul := (infinitesimalAutomorphisms_module_laws (p := p)).2.2.2.2.2

/-- Addition in unpointed `Inf(p)` agrees with composition of automorphisms. -/
theorem infinitesimalAutomorphisms_add_eq_mul [IsPredeformationCategory p]
    [HasRimSchlessinger p] (α β : infinitesimalAutomorphisms p) :
    α + β = α * β := rfl

end CategoryTheory.Functor

namespace CategoryTheory.BasedFunctor

variable {X Y : Type v} [Category.{w} X] [Category.{w} Y]
variable {p : X ⥤ ArtinianLocalAlgCat Λ k} {q : Y ⥤ ArtinianLocalAlgCat Λ k}
variable [IsPredeformationCategory p] [IsPredeformationCategory q]
variable [HasRimSchlessinger p] [HasRimSchlessinger q]

/-- The unpointed map on infinitesimal automorphisms induced by a morphism of predeformation
categories, obtained by conjugating `infAutLinearMap` along `infinitesimalAutomorphismsEquivAt`
at the chosen dual-number pushforwards. -/
def mapInfinitesimalAutomorphisms (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) :
    infinitesimalAutomorphisms p → infinitesimalAutomorphisms q :=
  fun α ↦
    let x0 := chosenResidueFiberObj p
    let x0' := pushforwardObj p (residueToDualNumber Λ k) x0
    let ψ := chosenDualNumberHom p x0
    let equivAt := infinitesimalAutomorphismsEquivAt q
      ((φ.fiberFunctor (residue Λ k)).obj x0)
      ((φ.fiberFunctor (dualNumber Λ k)).obj x0')
    (@equivAt (mapPushforward φ ψ) (mapPushforward_isStronglyCocartesian φ ψ)).symm
      (infAutLinearMap φ ψ (infinitesimalAutomorphismsEquivAt p x0 x0' ψ α))

/-- The unpointed infinitesimal-automorphism map is `k`-linear. -/
theorem isLinearMap_mapInfinitesimalAutomorphisms (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) :
    IsLinearMap k (mapInfinitesimalAutomorphisms φ) := sorry

/-- The unpointed `k`-linear map `Inf(p) ⟶ Inf(q)` induced by a morphism of predeformation
categories. -/
def mapInfinitesimalAutomorphismsLinearMap (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) :
    infinitesimalAutomorphisms p →ₗ[k] infinitesimalAutomorphisms q :=
  IsLinearMap.mk' (mapInfinitesimalAutomorphisms φ)
    (isLinearMap_mapInfinitesimalAutomorphisms φ)

/-- The underlying function of `mapInfinitesimalAutomorphismsLinearMap` is
`mapInfinitesimalAutomorphisms`. -/
theorem mapInfinitesimalAutomorphismsLinearMap_apply (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (α : infinitesimalAutomorphisms p) :
    mapInfinitesimalAutomorphismsLinearMap φ α = mapInfinitesimalAutomorphisms φ α := rfl

/-- `mapInfinitesimalAutomorphisms` conjugates `infAutLinearMap` along the chosen
`infinitesimalAutomorphismsEquivAt` identifications. -/
theorem mapInfinitesimalAutomorphisms_apply (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (α : infinitesimalAutomorphisms p) :
    mapInfinitesimalAutomorphisms φ α =
      let x0 := chosenResidueFiberObj p
      let x0' := pushforwardObj p (residueToDualNumber Λ k) x0
      let ψ := chosenDualNumberHom p x0
      let equivAt := infinitesimalAutomorphismsEquivAt q
        ((φ.fiberFunctor (residue Λ k)).obj x0)
        ((φ.fiberFunctor (dualNumber Λ k)).obj x0')
      (@equivAt (mapPushforward φ ψ) (mapPushforward_isStronglyCocartesian φ ψ)).symm
        (infAutLinearMap φ ψ (infinitesimalAutomorphismsEquivAt p x0 x0' ψ α)) := rfl

end CategoryTheory.BasedFunctor
