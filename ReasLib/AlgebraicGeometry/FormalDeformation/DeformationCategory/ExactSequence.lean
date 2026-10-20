/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Prod
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Projections
public import ReasLib.AlgebraicGeometry.FormalDeformation.Differential
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger.Schlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.FiberIsoClass
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Unpointed
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory.TwoFibreProduct

/-!
# The infinitesimal and tangent exact sequence of a two-fibre product

A cospan of deformation categories has a canonical six-term exact sequence.
Its boundary sends an infinitesimal automorphism to the fibre class obtained
by twisting the comparison of a chosen dual-number pushforward.
-/

-- Public fibre constructions use the private comparison verticality certificate.
set_option backward.privateInPublic true

@[expose] public section

noncomputable section

open CategoryTheory ArtinianLocalAlgCat Functor BasedCategory
open CofiberedCategoryOver.Groupoids
open scoped Bicategory BasedFunctor
open Fiber
open Functor.Chosen
open Limits

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.BasedFunctor

variable {F G H : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k)}
variable (f : H ⟶ F) (g : G ⟶ F)
variable [IsDeformationCategory F.p] [IsDeformationCategory G.p] [IsDeformationCategory H.p]

/-- The projection functor of the chosen 2-fibre product of `f` and `g`. -/
abbrev apexProjection :=
  CofiberedCategoryOver.Groupoids.p (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)

/-- The first `H`-leg of the chosen residue object of `W`, as a residue fibre object. -/
def connectingResidueFstFiber : H.p.Fiber (residue Λ k) :=
  let w0 := chosenResidueFiberObj (apexProjection f g)
  ⟨BasedCategory.PseudoPullback.fstObj w0.1,
    (BasedCategory.PseudoPullback.fiberObj w0.1).fst.2.trans w0.2⟩

/-- The first `H`-leg `y'0` of the chosen dual-number pushforward of `W`. -/
def connectingDualNumberFstFiber : H.p.Fiber (dualNumber Λ k) :=
  let w0' :=
    pushforwardObj (apexProjection f g) (residueToDualNumber Λ k)
      (chosenResidueFiberObj (apexProjection f g))
  ⟨BasedCategory.PseudoPullback.fstObj w0'.1,
    (BasedCategory.PseudoPullback.fiberObj w0'.1).fst.2.trans w0'.2⟩

/-- The second `G`-leg `z'0` of the chosen dual-number pushforward of `W`. -/
def connectingDualNumberSndFiber : G.p.Fiber (dualNumber Λ k) :=
  let w0' :=
    pushforwardObj (apexProjection f g) (residueToDualNumber Λ k)
      (chosenResidueFiberObj (apexProjection f g))
  ⟨BasedCategory.PseudoPullback.sndObj w0'.1,
    (BasedCategory.PseudoPullback.fiberObj w0'.1).snd.2.trans w0'.2⟩

/-- The morphism `f(y0) ⟶ f(y'0)` obtained by applying `f` to the first component of the
chosen dual-number pushforward of `W`. -/
def connectingLegPushforward :
    fiberInclusion.obj
        ((f.hom.fiberFunctor (residue Λ k)).obj (connectingResidueFstFiber f g)) ⟶
      fiberInclusion.obj
        ((f.hom.fiberFunctor (dualNumber Λ k)).obj (connectingDualNumberFstFiber f g)) :=
  f.hom.map
    (BasedCategory.PseudoPullback.fstMap
      (chosenDualNumberHom (apexProjection f g)
        (chosenResidueFiberObj (apexProjection f g))))

/-- The first-leg pushforward `f(y0) ⟶ f(y'0)` is strongly cocartesian over
`residueToDualNumber`. -/
instance instIsStronglyCocartesian_connectingLegPushforward :
    F.p.IsStronglyCocartesian (residueToDualNumber Λ k)
      (connectingLegPushforward f g) := sorry

/-- The original comparison `c' : f(y'0) ≅ g(z'0)` of the chosen dual-number pushforward of
`W` is vertical over the identity of `dualNumber`. -/
private theorem connectingComparison_isHomLift :
    F.p.IsHomLift (𝟙 (dualNumber Λ k))
      (BasedCategory.PseudoPullback.comparisonIsoApp
        (pushforwardObj (apexProjection f g) (residueToDualNumber Λ k)
          (chosenResidueFiberObj (apexProjection f g))).1).hom := sorry

/-- The original comparison `c'` of the chosen dual-number pushforward of `W`, as a fibre
isomorphism `f(y'0) ≅ g(z'0)`. -/
def connectingComparison :
    (f.hom.fiberFunctor (dualNumber Λ k)).obj (connectingDualNumberFstFiber f g) ≅
      (g.hom.fiberFunctor (dualNumber Λ k)).obj (connectingDualNumberSndFiber f g) :=
  Fiber.isoMk
    (BasedCategory.PseudoPullback.comparisonIsoApp
      (pushforwardObj (apexProjection f g) (residueToDualNumber Λ k)
        (chosenResidueFiberObj (apexProjection f g))).1)
    (connectingComparison_isHomLift f g)

/-- An infinitesimal automorphism of `F`, transported to an automorphism of the `F`-leg
`f(y'0)` of the chosen dual-number pushforward of `W`. -/
def connectingAut (α : infinitesimalAutomorphisms F.p) :
    Aut ((f.hom.fiberFunctor (dualNumber Λ k)).obj (connectingDualNumberFstFiber f g)) :=
  (infinitesimalAutomorphismsEquivAt F.p
      ((f.hom.fiberFunctor (residue Λ k)).obj (connectingResidueFstFiber f g))
      ((f.hom.fiberFunctor (dualNumber Λ k)).obj (connectingDualNumberFstFiber f g))
      (connectingLegPushforward f g) α).val

/-- The dual-number fibre object of `W` with legs `y'0 = fstObj` and `z'0 = sndObj` of the
chosen dual-number pushforward, and with comparison `c' ∘ α ∘ b'` under the normalization
`b' = 𝟙` and `x'0 = f(y'0)`, i.e. the transported automorphism of the `F`-leg followed by
the original comparison `c'`. -/
def connectingObj (α : infinitesimalAutomorphisms F.p) :
    (apexProjection f g).Fiber (dualNumber Λ k) :=
  ⟨BasedCategory.PseudoPullback.mk f.hom g.hom (dualNumber Λ k)
      ⟨connectingDualNumberFstFiber f g, connectingDualNumberSndFiber f g,
        connectingAut f g α ≪≫ connectingComparison f g⟩, rfl⟩

/-- The connecting map `δ : Inf(F) ⟶ T W` sending an infinitesimal automorphism of `F` to the
isomorphism class of `connectingObj`. -/
def connecting (α : infinitesimalAutomorphisms F.p) :
    (fiberIsoClassFunctor (apexProjection f g)).obj (dualNumber Λ k) :=
  Quotient.mk'' (connectingObj f g α)

/-- `connecting α` is the dual-number fibre class of the object with legs `fstObj`/`sndObj`
of the chosen dual-number pushforward of `W` and comparison `α.hom ≫ c'`, where `c'` is the
original comparison of that pushforward (normalization `b' = 𝟙`, `x'0 = f(y'0)`). -/
theorem connecting_mk (α : infinitesimalAutomorphisms F.p) :
    connecting f g α = Quotient.mk'' (connectingObj f g α) ∧
      BasedCategory.PseudoPullback.fstObj (connectingObj f g α).1 =
        (connectingDualNumberFstFiber f g).1 ∧
      BasedCategory.PseudoPullback.sndObj (connectingObj f g α).1 =
        (connectingDualNumberSndFiber f g).1 ∧
      BasedCategory.PseudoPullback.comparison (connectingObj f g α).1 =
        fiberInclusion.map (connectingAut f g α).hom ≫
          BasedCategory.PseudoPullback.comparison
            (pushforwardObj (apexProjection f g) (residueToDualNumber Λ k)
              (chosenResidueFiberObj (apexProjection f g))).1 := sorry

/-- The connecting map is `k`-linear. -/
theorem isLinearMap_connecting : IsLinearMap k (connecting f g) := sorry

/-- The bundled `k`-linear connecting map `Inf(F) ⟶ T W`. -/
def connectingLinearMap :
    infinitesimalAutomorphisms F.p →ₗ[k]
      (fiberIsoClassFunctor (apexProjection f g)).obj (dualNumber Λ k) :=
  IsLinearMap.mk' (connecting f g) (isLinearMap_connecting f g)

/-- The underlying function of `connectingLinearMap` is `connecting`. -/
theorem connectingLinearMap_apply (α : infinitesimalAutomorphisms F.p) :
    connectingLinearMap f g α = connecting f g α := rfl

/-- The map `Inf(W) ⟶ Inf(H) × Inf(G)` induced by the two projections of the 2-fibre product. -/
def infProdLinearMap :
    infinitesimalAutomorphisms (apexProjection f g) →ₗ[k]
      infinitesimalAutomorphisms H.p × infinitesimalAutomorphisms G.p :=
  LinearMap.prod
    (mapInfinitesimalAutomorphismsLinearMap
      (CofiberedCategoryOver.Groupoids.toBasedFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g)))
    (mapInfinitesimalAutomorphismsLinearMap
      (CofiberedCategoryOver.Groupoids.toBasedFunctor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)))

/-- `infProdLinearMap` is the pair of unpointed infinitesimal maps of the two projections. -/
theorem infProdLinearMap_apply (α : infinitesimalAutomorphisms (apexProjection f g)) :
    infProdLinearMap f g α =
      (mapInfinitesimalAutomorphisms
        (CofiberedCategoryOver.Groupoids.toBasedFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g)) α,
        mapInfinitesimalAutomorphisms
          (CofiberedCategoryOver.Groupoids.toBasedFunctor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)) α) := rfl

/-- The difference map `Inf(H) × Inf(G) ⟶ Inf(F)`, sending `(β, γ)` to `Inf(f)(β) - Inf(g)(γ)`. -/
def infDiffLinearMap :
    infinitesimalAutomorphisms H.p × infinitesimalAutomorphisms G.p →ₗ[k]
      infinitesimalAutomorphisms F.p :=
  LinearMap.coprod
    (mapInfinitesimalAutomorphismsLinearMap (CofiberedCategoryOver.Groupoids.toBasedFunctor f))
    (-mapInfinitesimalAutomorphismsLinearMap (CofiberedCategoryOver.Groupoids.toBasedFunctor g))

/-- `infDiffLinearMap` evaluates as `Inf(f)(β) - Inf(g)(γ)`. -/
theorem infDiffLinearMap_apply (β : infinitesimalAutomorphisms H.p)
    (γ : infinitesimalAutomorphisms G.p) :
    infDiffLinearMap f g (β, γ) =
      mapInfinitesimalAutomorphisms (CofiberedCategoryOver.Groupoids.toBasedFunctor f) β -
        mapInfinitesimalAutomorphisms (CofiberedCategoryOver.Groupoids.toBasedFunctor g) γ := by
  exact (sub_eq_add_neg
    (mapInfinitesimalAutomorphisms (CofiberedCategoryOver.Groupoids.toBasedFunctor f) β)
    (mapInfinitesimalAutomorphisms (CofiberedCategoryOver.Groupoids.toBasedFunctor g) γ)).symm

/-- The differential `T W ⟶ T H × T G` of the two projections of the 2-fibre product. -/
def tangentProdLinearMap :
    (fiberIsoClassFunctor (apexProjection f g)).obj (dualNumber Λ k) →ₗ[k]
      (fiberIsoClassFunctor H.p).obj (dualNumber Λ k) ×
        (fiberIsoClassFunctor G.p).obj (dualNumber Λ k) :=
  LinearMap.prod
    (differentialLinearMap
      (CofiberedCategoryOver.Groupoids.toBasedFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g)))
    (differentialLinearMap
      (CofiberedCategoryOver.Groupoids.toBasedFunctor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)))

/-- `tangentProdLinearMap` is the pair of differentials of the two projections. -/
theorem tangentProdLinearMap_apply
    (x : (fiberIsoClassFunctor (apexProjection f g)).obj (dualNumber Λ k)) :
    tangentProdLinearMap f g x =
      (differential
        (CofiberedCategoryOver.Groupoids.toBasedFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g)) x,
        differential
          (CofiberedCategoryOver.Groupoids.toBasedFunctor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)) x) := rfl

/-- The difference of differentials `T H × T G ⟶ T F`, sending `(y, z)` to `df(y) - dg(z)`. -/
def tangentDiffLinearMap :
    (fiberIsoClassFunctor H.p).obj (dualNumber Λ k) ×
        (fiberIsoClassFunctor G.p).obj (dualNumber Λ k) →ₗ[k]
      (fiberIsoClassFunctor F.p).obj (dualNumber Λ k) :=
  LinearMap.coprod
    (differentialLinearMap (CofiberedCategoryOver.Groupoids.toBasedFunctor f))
    (-differentialLinearMap (CofiberedCategoryOver.Groupoids.toBasedFunctor g))

/-- `tangentDiffLinearMap` evaluates as `df(y) - dg(z)`. -/
theorem tangentDiffLinearMap_apply
    (y : (fiberIsoClassFunctor H.p).obj (dualNumber Λ k))
    (z : (fiberIsoClassFunctor G.p).obj (dualNumber Λ k)) :
    tangentDiffLinearMap f g (y, z) =
      Sub.sub (α := (fiberIsoClassFunctor F.p).obj (dualNumber Λ k))
        (differential (CofiberedCategoryOver.Groupoids.toBasedFunctor f) y)
        (differential (CofiberedCategoryOver.Groupoids.toBasedFunctor g) z) := by
  exact (sub_eq_add_neg (G := (fiberIsoClassFunctor F.p).obj (dualNumber Λ k))
    (differential (CofiberedCategoryOver.Groupoids.toBasedFunctor f) y)
    (differential (CofiberedCategoryOver.Groupoids.toBasedFunctor g) z)).symm

/-- The first nonzero map of the six-term sequence is injective. -/
theorem infProdLinearMap_injective : Function.Injective (infProdLinearMap f g) := sorry

/-- Exactness of the six-term sequence at `Inf(H) × Inf(G)`. -/
theorem exact_infProd_infDiff : Function.Exact (infProdLinearMap f g) (infDiffLinearMap f g) :=
  sorry

/-- Exactness of the six-term sequence at `Inf(F)`. -/
theorem exact_infDiff_connecting :
    Function.Exact (infDiffLinearMap f g) (connectingLinearMap f g) := sorry

/-- Exactness of the six-term sequence at `T W`. -/
theorem exact_connecting_tangentProd :
    Function.Exact (connectingLinearMap f g) (tangentProdLinearMap f g) := sorry

/-- Exactness of the six-term sequence at `T H × T G`. -/
theorem exact_tangentProd_tangentDiff :
    Function.Exact (tangentProdLinearMap f g) (tangentDiffLinearMap f g) := sorry

/-- For a cospan of deformation categories, the canonical six-term infinitesimal and
tangent sequence is exact, with injective first map. -/
theorem infTangentSequence_exact
    {F G H : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k)}
    (f : H ⟶ F) (g : G ⟶ F)
    [IsDeformationCategory F.p] [IsDeformationCategory G.p] [IsDeformationCategory H.p] :
    Function.Injective (infProdLinearMap f g) ∧
      Function.Exact (infProdLinearMap f g) (infDiffLinearMap f g) ∧
      Function.Exact (infDiffLinearMap f g) (connectingLinearMap f g) ∧
      Function.Exact (connectingLinearMap f g) (tangentProdLinearMap f g) ∧
      Function.Exact (tangentProdLinearMap f g) (tangentDiffLinearMap f g) :=
  ⟨infProdLinearMap_injective f g, exact_infProd_infDiff f g,
    exact_infDiff_connecting f g, exact_connecting_tangentProd f g,
    exact_tangentProd_tangentDiff f g⟩

end CategoryTheory.BasedFunctor
