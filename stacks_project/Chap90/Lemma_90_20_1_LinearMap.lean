module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Prod
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Projections
public import stacks_project.Chap90.Lemma_90_12_4
public import stacks_project.Chap90.Lemma_90_16_6
public import stacks_project.Chap90.Lemma_90_19_10_LinearMap
public import stacks_project.Chap90.Lemma_90_20_1_Instances
public import stacks_project.Chap90.Remark_90_19_4_InfinitesimalAut

/-!
# Infinitesimal and tangent maps of a 2-fibre product of deformation categories

Unpointed `k`-linear maps on `Inf` and `T`, together with the connecting map
`Inf(F) ⟶ T W` of a cospan of deformation categories.
-/

@[expose] public section

noncomputable section

open CategoryTheory ArtinianLocalAlgCat Functor BasedCategory
open CofiberedCategoryOver.Groupoids
open scoped Bicategory BasedFunctor
open Fiber
open Functor.Chosen
open Limits

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

/-- The additive group structure on unpointed `Inf(p)`. -/
instance instAddCommGroup_infinitesimalAutomorphisms [IsPredeformationCategory p]
    [HasRimSchlessinger p] : AddCommGroup (infinitesimalAutomorphisms p) where
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := nsmulRec
  neg_add_cancel := sorry
  zsmul := zsmulRec
  add_comm := sorry

/-- The `k`-vector space structure on unpointed `Inf(p)`, transported from
`instModule_infinitesimalAutomorphismsAt`. -/
instance instModule_infinitesimalAutomorphisms [IsPredeformationCategory p]
    [HasRimSchlessinger p] : Module k (infinitesimalAutomorphisms p) where
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- Addition in unpointed `Inf(p)` agrees with composition of automorphisms. -/
theorem infinitesimalAutomorphisms_add_eq_mul [IsPredeformationCategory p]
    [HasRimSchlessinger p] (α β : infinitesimalAutomorphisms p) :
    α + β = α * β := sorry

/-- A predeformation category satisfying (S2) has isomorphism-class functor satisfying (H2). -/
instance instHasSchlessingerH2_fiberIsoClass [IsPredeformationCategory p]
    [HasSchlessingerS2 p] : HasSchlessingerH2 (fiberIsoClassFunctor p) := sorry

/-- The `ofFunctor` presentation of a predeformation category is a predeformation category. -/
instance instIsPredeformationCategory_ofFunctor
    {F : Type v} [Category.{w} F] (r : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsPredeformationCategory r] :
    IsPredeformationCategory (BasedCategory.ofFunctor r).p :=
  inferInstanceAs (IsPredeformationCategory r)

/-- Deformation categories satisfy the Rim-Schlessinger condition. -/
instance instHasRimSchlessinger_ofIsDeformationCategory [IsDeformationCategory p] :
    HasRimSchlessinger p :=
  IsDeformationCategory.hasRimSchlessinger

end CategoryTheory.Functor

namespace CategoryTheory.CofiberedCategoryOver.Groupoids

variable {F G H : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k)}

/-- Convert a morphism of categories cofibered in groupoids into a based functor between the
`ofFunctor` presentations of the projections. -/
def toOfFunctor (φ : F ⟶ G) :
    BasedCategory.ofFunctor F.p ⥤ᵇ BasedCategory.ofFunctor G.p :=
  BasedFunctor.ofFunctor (toBasedFunctor φ).toFunctor (toBasedFunctor φ).w

/-- `toOfFunctor` is the `ofFunctor` packaging of the underlying total-category functor. -/
theorem toOfFunctor_toFunctor (φ : F ⟶ G) :
    (toOfFunctor φ).toFunctor = (toBasedFunctor φ).toFunctor := sorry

end CategoryTheory.CofiberedCategoryOver.Groupoids

namespace CategoryTheory.BasedFunctor

variable {X Y : Type v} [Category.{w} X] [Category.{w} Y]
variable {p : X ⥤ ArtinianLocalAlgCat Λ k} {q : Y ⥤ ArtinianLocalAlgCat Λ k}
variable [IsPredeformationCategory p] [IsPredeformationCategory q]
variable [HasRimSchlessinger p] [HasRimSchlessinger q]

/-- The image of a dual-number pushforward under an `ofFunctor` based functor is strongly
cocartesian over `residueToDualNumber` as a morphism of the target projection. -/
instance instIsStronglyCocartesian_mapPushforward
    (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    {x0 : p.Fiber (residue Λ k)} {x0' : p.Fiber (dualNumber Λ k)}
    (ψ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ] :
    q.IsStronglyCocartesian (residueToDualNumber Λ k) (mapPushforward φ ψ) := sorry

/-- The unpointed map on infinitesimal automorphisms induced by a morphism of predeformation
categories, obtained by conjugating `infAutLinearMap` along `infinitesimalAutomorphismsEquivAt`
at the chosen dual-number pushforwards. -/
def mapInfinitesimalAutomorphisms (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) :
    infinitesimalAutomorphisms p → infinitesimalAutomorphisms q :=
  fun α ↦
    let x0 := chosenResidueFiberObj p
    let x0' := pushforwardObj p (residueToDualNumber Λ k) x0
    let ψ := chosenDualNumberHom p x0
    (infinitesimalAutomorphismsEquivAt (BasedCategory.ofFunctor q).p ((φ.fiberFunctor (residue Λ k)).obj x0)
          ((φ.fiberFunctor (dualNumber Λ k)).obj x0') (mapPushforward φ ψ)).symm
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
    mapInfinitesimalAutomorphismsLinearMap φ α = mapInfinitesimalAutomorphisms φ α := sorry

/-- `mapInfinitesimalAutomorphisms` conjugates `infAutLinearMap` along the chosen
`infinitesimalAutomorphismsEquivAt` identifications. -/
theorem mapInfinitesimalAutomorphisms_apply (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (α : infinitesimalAutomorphisms p) :
    mapInfinitesimalAutomorphisms φ α =
      let x0 := chosenResidueFiberObj p
      let x0' := pushforwardObj p (residueToDualNumber Λ k) x0
      let ψ := chosenDualNumberHom p x0
      (infinitesimalAutomorphismsEquivAt (BasedCategory.ofFunctor q).p ((φ.fiberFunctor (residue Λ k)).obj x0)
            ((φ.fiberFunctor (dualNumber Λ k)).obj x0') (mapPushforward φ ψ)).symm
        (infAutLinearMap φ ψ (infinitesimalAutomorphismsEquivAt p x0 x0' ψ α)) := sorry

end CategoryTheory.BasedFunctor

namespace CategoryTheory.BasedFunctor

variable {F G H : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k)}
variable (f : H ⟶ F) (g : G ⟶ F)
variable [IsDeformationCategory F.p] [IsDeformationCategory G.p] [IsDeformationCategory H.p]

/-- The projection functor of the chosen 2-fibre product of `f` and `g`. -/
abbrev apexProjection :=
  CofiberedCategoryOver.Groupoids.p (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)

/-- `apexProjection f g` is the projection of `TwoFibreProduct.apex f g`. -/
theorem apexProjection_eq :
    apexProjection f g =
      CofiberedCategoryOver.Groupoids.p (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g) := sorry

/-- The first `H`-leg of the chosen residue object of `W`, as a residue fibre object. -/
def connectingResidueFstFiber : H.p.Fiber (residue Λ k) :=
  let w0 := chosenResidueFiberObj (apexProjection f g)
  ⟨BasedCategory.PseudoPullback.fstObj w0.1,
    (BasedCategory.PseudoPullback.fiberObj w0.1).fst.2.trans w0.2⟩

/-- The underlying object of `connectingResidueFstFiber` is the first projection of the chosen
residue object of `W`. -/
theorem connectingResidueFstFiber_obj :
    (connectingResidueFstFiber f g).1 =
      BasedCategory.PseudoPullback.fstObj
        (chosenResidueFiberObj (apexProjection f g)).1 := sorry

/-- The first `H`-leg `y'0` of the chosen dual-number pushforward of `W`. -/
def connectingDualNumberFstFiber : H.p.Fiber (dualNumber Λ k) :=
  let w0' :=
    pushforwardObj (apexProjection f g) (residueToDualNumber Λ k)
      (chosenResidueFiberObj (apexProjection f g))
  ⟨BasedCategory.PseudoPullback.fstObj w0'.1,
    (BasedCategory.PseudoPullback.fiberObj w0'.1).fst.2.trans w0'.2⟩

/-- The underlying object of `connectingDualNumberFstFiber` is `fstObj` of the chosen
dual-number pushforward of `W`. -/
theorem connectingDualNumberFstFiber_obj :
    (connectingDualNumberFstFiber f g).1 =
      BasedCategory.PseudoPullback.fstObj
        (pushforwardObj (apexProjection f g) (residueToDualNumber Λ k)
          (chosenResidueFiberObj (apexProjection f g))).1 := sorry

/-- The second `G`-leg `z'0` of the chosen dual-number pushforward of `W`. -/
def connectingDualNumberSndFiber : G.p.Fiber (dualNumber Λ k) :=
  let w0' :=
    pushforwardObj (apexProjection f g) (residueToDualNumber Λ k)
      (chosenResidueFiberObj (apexProjection f g))
  ⟨BasedCategory.PseudoPullback.sndObj w0'.1,
    (BasedCategory.PseudoPullback.fiberObj w0'.1).snd.2.trans w0'.2⟩

/-- The underlying object of `connectingDualNumberSndFiber` is `sndObj` of the chosen
dual-number pushforward of `W`. -/
theorem connectingDualNumberSndFiber_obj :
    (connectingDualNumberSndFiber f g).1 =
      BasedCategory.PseudoPullback.sndObj
        (pushforwardObj (apexProjection f g) (residueToDualNumber Λ k)
          (chosenResidueFiberObj (apexProjection f g))).1 := sorry

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

/-- `connectingLegPushforward` is `f` applied to the first component of the chosen dual-number
pushforward of `W`. -/
theorem connectingLegPushforward_apply :
    connectingLegPushforward f g =
      f.hom.map
        (BasedCategory.PseudoPullback.fstMap
          (chosenDualNumberHom (apexProjection f g)
            (chosenResidueFiberObj (apexProjection f g)))) := sorry

/-- The first-leg pushforward `f(y0) ⟶ f(y'0)` is strongly cocartesian over
`residueToDualNumber`. -/
instance instIsStronglyCocartesian_connectingLegPushforward :
    F.p.IsStronglyCocartesian (residueToDualNumber Λ k)
      (connectingLegPushforward f g) := sorry

/-- The original comparison `c' : f(y'0) ≅ g(z'0)` of the chosen dual-number pushforward of
`W` is vertical over the identity of `dualNumber`. -/
theorem connectingComparison_isHomLift :
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

/-- `connectingComparison` is the fibre packaging of `comparisonIsoApp` of the chosen
dual-number pushforward of `W`. -/
theorem connectingComparison_hom :
    fiberInclusion.map (connectingComparison f g).hom =
      (BasedCategory.PseudoPullback.comparisonIsoApp
        (pushforwardObj (apexProjection f g) (residueToDualNumber Λ k)
          (chosenResidueFiberObj (apexProjection f g))).1).hom := sorry

/-- An infinitesimal automorphism of `F`, transported to an automorphism of the `F`-leg
`f(y'0)` of the chosen dual-number pushforward of `W`. -/
def connectingAut (α : infinitesimalAutomorphisms F.p) :
    Aut ((f.hom.fiberFunctor (dualNumber Λ k)).obj (connectingDualNumberFstFiber f g)) :=
  (infinitesimalAutomorphismsEquivAt F.p
      ((f.hom.fiberFunctor (residue Λ k)).obj (connectingResidueFstFiber f g))
      ((f.hom.fiberFunctor (dualNumber Λ k)).obj (connectingDualNumberFstFiber f g))
      (connectingLegPushforward f g) α).val

/-- `connectingAut` is `infinitesimalAutomorphismsEquivAt` at the `F`-leg `f(y'0)`. -/
theorem connectingAut_apply (α : infinitesimalAutomorphisms F.p) :
    connectingAut f g α =
      (infinitesimalAutomorphismsEquivAt F.p
          ((f.hom.fiberFunctor (residue Λ k)).obj (connectingResidueFstFiber f g))
          ((f.hom.fiberFunctor (dualNumber Λ k)).obj (connectingDualNumberFstFiber f g))
          (connectingLegPushforward f g) α).val := sorry

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
    connectingLinearMap f g α = connecting f g α := sorry

/-- The map `Inf(W) ⟶ Inf(H) × Inf(G)` induced by the two projections of the 2-fibre product. -/
def infProdLinearMap :
    infinitesimalAutomorphisms (apexProjection f g) →ₗ[k]
      infinitesimalAutomorphisms H.p × infinitesimalAutomorphisms G.p :=
  LinearMap.prod
    (mapInfinitesimalAutomorphismsLinearMap
      (CofiberedCategoryOver.Groupoids.toOfFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g)))
    (mapInfinitesimalAutomorphismsLinearMap
      (CofiberedCategoryOver.Groupoids.toOfFunctor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)))

/-- `infProdLinearMap` is the pair of unpointed infinitesimal maps of the two projections. -/
theorem infProdLinearMap_apply (α : infinitesimalAutomorphisms (apexProjection f g)) :
    infProdLinearMap f g α =
      (mapInfinitesimalAutomorphisms
        (CofiberedCategoryOver.Groupoids.toOfFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g)) α,
        mapInfinitesimalAutomorphisms
          (CofiberedCategoryOver.Groupoids.toOfFunctor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)) α) := sorry

/-- The difference map `Inf(H) × Inf(G) ⟶ Inf(F)`, sending `(β, γ)` to `Inf(f)(β) - Inf(g)(γ)`. -/
def infDiffLinearMap :
    infinitesimalAutomorphisms H.p × infinitesimalAutomorphisms G.p →ₗ[k]
      infinitesimalAutomorphisms F.p :=
  LinearMap.coprod
    (mapInfinitesimalAutomorphismsLinearMap (CofiberedCategoryOver.Groupoids.toOfFunctor f))
    (-mapInfinitesimalAutomorphismsLinearMap (CofiberedCategoryOver.Groupoids.toOfFunctor g))

/-- `infDiffLinearMap` evaluates as `Inf(f)(β) - Inf(g)(γ)`. -/
theorem infDiffLinearMap_apply (β : infinitesimalAutomorphisms H.p)
    (γ : infinitesimalAutomorphisms G.p) :
    infDiffLinearMap f g (β, γ) =
      mapInfinitesimalAutomorphisms (CofiberedCategoryOver.Groupoids.toOfFunctor f) β -
        mapInfinitesimalAutomorphisms (CofiberedCategoryOver.Groupoids.toOfFunctor g) γ := sorry

/-- The differential `T W ⟶ T H × T G` of the two projections of the 2-fibre product. -/
def tangentProdLinearMap :
    (fiberIsoClassFunctor (apexProjection f g)).obj (dualNumber Λ k) →ₗ[k]
      (fiberIsoClassFunctor H.p).obj (dualNumber Λ k) ×
        (fiberIsoClassFunctor G.p).obj (dualNumber Λ k) :=
  LinearMap.prod
    (differentialLinearMap
      (CofiberedCategoryOver.Groupoids.toOfFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g)))
    (differentialLinearMap
      (CofiberedCategoryOver.Groupoids.toOfFunctor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)))

/-- `tangentProdLinearMap` is the pair of differentials of the two projections. -/
theorem tangentProdLinearMap_apply
    (x : (fiberIsoClassFunctor (apexProjection f g)).obj (dualNumber Λ k)) :
    tangentProdLinearMap f g x =
      (differential
        (CofiberedCategoryOver.Groupoids.toOfFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g)) x,
        differential
          (CofiberedCategoryOver.Groupoids.toOfFunctor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)) x) := sorry

/-- The difference of differentials `T H × T G ⟶ T F`, sending `(y, z)` to `df(y) - dg(z)`. -/
def tangentDiffLinearMap :
    (fiberIsoClassFunctor H.p).obj (dualNumber Λ k) ×
        (fiberIsoClassFunctor G.p).obj (dualNumber Λ k) →ₗ[k]
      (fiberIsoClassFunctor F.p).obj (dualNumber Λ k) :=
  LinearMap.coprod
    (differentialLinearMap (CofiberedCategoryOver.Groupoids.toOfFunctor f))
    (-differentialLinearMap (CofiberedCategoryOver.Groupoids.toOfFunctor g))

/-- `tangentDiffLinearMap` evaluates as `df(y) - dg(z)`. -/
theorem tangentDiffLinearMap_apply
    (y : (fiberIsoClassFunctor H.p).obj (dualNumber Λ k))
    (z : (fiberIsoClassFunctor G.p).obj (dualNumber Λ k)) :
    tangentDiffLinearMap f g (y, z) =
      differential (CofiberedCategoryOver.Groupoids.toOfFunctor f) y -
        differential (CofiberedCategoryOver.Groupoids.toOfFunctor g) z := sorry

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

end CategoryTheory.BasedFunctor
