/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Prod
public import stacks_project.Chap90.Lemma_90_20_1_LinearMap
public import stacks_project.Chap98.Lemma_98_3_3
public import stacks_project.Chap98.Lemma_98_5_3
public import stacks_project.Chap98.Lemma_98_6_1

/-!
# Infinitesimal and tangent maps of a 2-fibre product over `(Sch/S)_fppf`

Unpointed `k`-linear maps on `Inf(ℱ_{-, k, -})` and `Tℱ_{-, k, -}` for
`W = X ×_Y Z`, together with the connecting map obtained from the 2-fibre product
of the associated predeformation categories.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry ArtinianLocalAlgCat
open FiberedCategoryOver.Groupoids
open scoped Bicategory BasedFunctor

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {X Y Z : GroupoidsOver S}

/-- The 2-fibre product `W = X ×_Y Z`. -/
abbrev fibreProduct (p : X ⟶ Y) (q : Z ⟶ Y) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} p q

/-- The object `x0` of `X` obtained from `w0` by the first projection of `W`. -/
abbrev imageX {kToS : Spec (CommRingCat.of k) ⟶ S} [LocallyOfFiniteType kToS]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (p : X ⟶ Y) (q : Z ⟶ Y) (w0 : (fibreProduct p q).p.Fiber (Over.mk kToS)) :
    X.p.Fiber (Over.mk kToS) :=
  residueImage (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) w0

/-- The object `z0` of `Z` obtained from `w0` by the second projection of `W`. -/
abbrev imageZ {kToS : Spec (CommRingCat.of k) ⟶ S} [LocallyOfFiniteType kToS]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (p : X ⟶ Y) (q : Z ⟶ Y) (w0 : (fibreProduct p q).p.Fiber (Over.mk kToS)) :
    Z.p.Fiber (Over.mk kToS) :=
  residueImage (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q) w0

/-- The object `y0` of `Y` obtained from `w0`. -/
abbrev imageY {kToS : Spec (CommRingCat.of k) ⟶ S} [LocallyOfFiniteType kToS]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (p : X ⟶ Y) (q : Z ⟶ Y) (w0 : (fibreProduct p q).p.Fiber (Over.mk kToS)) :
    Y.p.Fiber (Over.mk kToS) :=
  residueImage p (imageX openImmersion p q w0)

/-- Residue-fibre identification `q(z0) ≅ y0` extracted from the 2-cell of `W`. -/
abbrev fibreProductResidueIso {kToS : Spec (CommRingCat.of k) ⟶ S} [LocallyOfFiniteType kToS]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (p : X ⟶ Y) (q : Z ⟶ Y) (w0 : (fibreProduct p q).p.Fiber (Over.mk kToS)) :
    residueImage q (imageZ openImmersion p q w0) ≅
      imageY openImmersion p q w0 :=
  residueIso kToS p q (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q)
    (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q) (TwoFibreProduct.comparisonIso p q) w0

/-- The 1-morphism `ℱ_{W, k, w0} ⟶ ℱ_{X, k, x0}` induced by the first projection. -/
abbrev mapFst {kToS : Spec (CommRingCat.of k) ⟶ S} [LocallyOfFiniteType kToS]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (p : X ⟶ Y) (q : Z ⟶ Y) (w0 : (fibreProduct p q).p.Fiber (Over.mk kToS)) :
    bundled openImmersion kToS h_factor (fibreProduct p q) w0 ⟶
      bundled openImmersion kToS h_factor X (imageX openImmersion p q w0) :=
  mapBundled openImmersion kToS h_factor
    (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) w0

/-- The 1-morphism `ℱ_{W, k, w0} ⟶ ℱ_{Z, k, z0}` induced by the second projection. -/
abbrev mapSnd {kToS : Spec (CommRingCat.of k) ⟶ S} [LocallyOfFiniteType kToS]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (p : X ⟶ Y) (q : Z ⟶ Y) (w0 : (fibreProduct p q).p.Fiber (Over.mk kToS)) :
    bundled openImmersion kToS h_factor (fibreProduct p q) w0 ⟶
      bundled openImmersion kToS h_factor Z (imageZ openImmersion p q w0) :=
  mapBundled openImmersion kToS h_factor
    (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q) w0

/-- The 1-morphism `ℱ_{X, k, x0} ⟶ ℱ_{Y, k, y0}` induced by `p`. -/
abbrev mapP {kToS : Spec (CommRingCat.of k) ⟶ S} [LocallyOfFiniteType kToS]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (p : X ⟶ Y) (q : Z ⟶ Y) (w0 : (fibreProduct p q).p.Fiber (Over.mk kToS)) :
    bundled openImmersion kToS h_factor X (imageX openImmersion p q w0) ⟶
      bundled openImmersion kToS h_factor Y (imageY openImmersion p q w0) :=
  mapBundled openImmersion kToS h_factor p (imageX openImmersion p q w0)

/-- The 1-morphism `ℱ_{Z, k, z0} ⟶ ℱ_{Y, k, y0}` induced by `q` along `q(z0) ≅ y0`. -/
abbrev mapQ {kToS : Spec (CommRingCat.of k) ⟶ S} [LocallyOfFiniteType kToS]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (p : X ⟶ Y) (q : Z ⟶ Y) (w0 : (fibreProduct p q).p.Fiber (Over.mk kToS)) :
    bundled openImmersion kToS h_factor Z (imageZ openImmersion p q w0) ⟶
      bundled openImmersion kToS h_factor Y (imageY openImmersion p q w0) :=
  mapAlong openImmersion kToS h_factor q
    (fibreProductResidueIso openImmersion p q w0)

/-- The 2-fibre product of `ℱ_{X, k, x0}` and `ℱ_{Z, k, z0}` over `ℱ_{Y, k, y0}`. -/
abbrev predeformationApex {kToS : Spec (CommRingCat.of k) ⟶ S} [LocallyOfFiniteType kToS]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (p : X ⟶ Y) (q : Z ⟶ Y) (w0 : (fibreProduct p q).p.Fiber (Over.mk kToS)) :
    CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k) :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u}
    (mapP openImmersion h_factor p q w0) (mapQ openImmersion h_factor p q w0)

/-- Canonical comparison `ℱ_{W, k, w0} ⟶ predeformationApex`. -/
abbrev fibreProductComparison {kToS : Spec (CommRingCat.of k) ⟶ S} [LocallyOfFiniteType kToS]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (p : X ⟶ Y) (q : Z ⟶ Y) (w0 : (fibreProduct p q).p.Fiber (Over.mk kToS)) :
    bundled openImmersion kToS h_factor (fibreProduct p q) w0 ⟶
      predeformationApex openImmersion h_factor p q w0 :=
  comparison openImmersion kToS h_factor p q
    (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q)
    (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q)
    (TwoFibreProduct.comparisonIso p q) w0

variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
variable (p : X ⟶ Y) (q : Z ⟶ Y)
variable [HasRimSchlessinger X] [HasRimSchlessinger Y] [HasRimSchlessinger Z]
variable (w0 : (fibreProduct p q).p.Fiber (Over.mk kToS))

/-- The projection of `bundled X x0` is a deformation category whenever `X` satisfies (RS). -/
instance instIsDeformationCategory_bundled (W : GroupoidsOver S) [HasRimSchlessinger W]
    (w : W.p.Fiber (Over.mk kToS)) :
    Functor.IsDeformationCategory (bundled openImmersion kToS h_factor W w).p :=
  inferInstanceAs
    (Functor.IsDeformationCategory (predeformationFunctor W openImmersion kToS h_factor w))

/-- The differential of `fibreProductComparison` is bijective. -/
theorem bijective_differential_fibreProductComparison :
    Function.Bijective
      (BasedFunctor.differentialLinearMap
        (CofiberedCategoryOver.Groupoids.toOfFunctor
          (fibreProductComparison openImmersion h_factor p q w0))) :=
  sorry

/-- Linear equivalence `Tℱ_{W, k, w0} ≃ₗ[k] T(predeformationApex)` induced by the
comparison 1-morphism of predeformation categories. -/
def tangentComparisonLinearEquiv :
    (Functor.fiberIsoClassFunctor
          (bundled openImmersion kToS h_factor (fibreProduct p q) w0).p).obj
        (dualNumber Λ k) ≃ₗ[k]
      (Functor.fiberIsoClassFunctor
          (predeformationApex openImmersion h_factor p q w0).p).obj (dualNumber Λ k) :=
  LinearEquiv.ofBijective
    (BasedFunctor.differentialLinearMap
      (CofiberedCategoryOver.Groupoids.toOfFunctor
        (fibreProductComparison openImmersion h_factor p q w0)))
    (bijective_differential_fibreProductComparison openImmersion kToS h_factor p q w0)

/-- `tangentComparisonLinearEquiv` is the differential of `fibreProductComparison`. -/
theorem tangentComparisonLinearEquiv_apply
    (x : (Functor.fiberIsoClassFunctor
        (bundled openImmersion kToS h_factor (fibreProduct p q) w0).p).obj (dualNumber Λ k)) :
    tangentComparisonLinearEquiv openImmersion kToS h_factor p q w0 x =
      BasedFunctor.differential
        (CofiberedCategoryOver.Groupoids.toOfFunctor
          (fibreProductComparison openImmersion h_factor p q w0)) x :=
  sorry

/-- The map `Inf(ℱ_{W, k, w0}) ⟶ Inf(ℱ_{X, k, x0}) × Inf(ℱ_{Z, k, z0})` induced by the
two projections of `W`. -/
def infProdLinearMap :
    Functor.infinitesimalAutomorphisms
        (bundled openImmersion kToS h_factor (fibreProduct p q) w0).p →ₗ[k]
      Functor.infinitesimalAutomorphisms
          (bundled openImmersion kToS h_factor X (imageX openImmersion p q w0)).p ×
        Functor.infinitesimalAutomorphisms
          (bundled openImmersion kToS h_factor Z (imageZ openImmersion p q w0)).p :=
  LinearMap.prod
    (BasedFunctor.mapInfinitesimalAutomorphismsLinearMap
      (CofiberedCategoryOver.Groupoids.toOfFunctor
        (mapFst openImmersion h_factor p q w0)))
    (BasedFunctor.mapInfinitesimalAutomorphismsLinearMap
      (CofiberedCategoryOver.Groupoids.toOfFunctor
        (mapSnd openImmersion h_factor p q w0)))

/-- `infProdLinearMap` is the pair of unpointed infinitesimal maps of the two projections. -/
theorem infProdLinearMap_apply
    (α : Functor.infinitesimalAutomorphisms
        (bundled openImmersion kToS h_factor (fibreProduct p q) w0).p) :
    infProdLinearMap openImmersion kToS h_factor p q w0 α =
      (BasedFunctor.mapInfinitesimalAutomorphisms
        (CofiberedCategoryOver.Groupoids.toOfFunctor
          (mapFst openImmersion h_factor p q w0)) α,
        BasedFunctor.mapInfinitesimalAutomorphisms
          (CofiberedCategoryOver.Groupoids.toOfFunctor
            (mapSnd openImmersion h_factor p q w0)) α) :=
  sorry

/-- The difference map `Inf(ℱ_{X, k, x0}) × Inf(ℱ_{Z, k, z0}) ⟶ Inf(ℱ_{Y, k, y0})`,
sending `(β, γ)` to `Inf(p)(β) - Inf(q)(γ)`. -/
def infDiffLinearMap :
    Functor.infinitesimalAutomorphisms
          (bundled openImmersion kToS h_factor X (imageX openImmersion p q w0)).p ×
        Functor.infinitesimalAutomorphisms
          (bundled openImmersion kToS h_factor Z (imageZ openImmersion p q w0)).p →ₗ[k]
      Functor.infinitesimalAutomorphisms
        (bundled openImmersion kToS h_factor Y (imageY openImmersion p q w0)).p :=
  LinearMap.coprod
    (BasedFunctor.mapInfinitesimalAutomorphismsLinearMap
      (CofiberedCategoryOver.Groupoids.toOfFunctor
        (mapP openImmersion h_factor p q w0)))
    (-BasedFunctor.mapInfinitesimalAutomorphismsLinearMap
      (CofiberedCategoryOver.Groupoids.toOfFunctor
        (mapQ openImmersion h_factor p q w0)))

/-- `infDiffLinearMap` evaluates as `Inf(p)(β) - Inf(q)(γ)`. -/
theorem infDiffLinearMap_apply
    (β : Functor.infinitesimalAutomorphisms
        (bundled openImmersion kToS h_factor X (imageX openImmersion p q w0)).p)
    (γ : Functor.infinitesimalAutomorphisms
        (bundled openImmersion kToS h_factor Z (imageZ openImmersion p q w0)).p) :
    infDiffLinearMap openImmersion kToS h_factor p q w0 (β, γ) =
      BasedFunctor.mapInfinitesimalAutomorphisms
          (CofiberedCategoryOver.Groupoids.toOfFunctor
            (mapP openImmersion h_factor p q w0)) β -
        BasedFunctor.mapInfinitesimalAutomorphisms
          (CofiberedCategoryOver.Groupoids.toOfFunctor
            (mapQ openImmersion h_factor p q w0)) γ :=
  sorry

/-- The connecting map `Inf(ℱ_{Y, k, y0}) ⟶ Tℱ_{W, k, w0}`, obtained by transporting
`BasedFunctor.connectingLinearMap` of the image cospan along the inverse of
`d(fibreProductComparison)`. -/
def connectingLinearMap :
    Functor.infinitesimalAutomorphisms
        (bundled openImmersion kToS h_factor Y (imageY openImmersion p q w0)).p →ₗ[k]
      (Functor.fiberIsoClassFunctor
          (bundled openImmersion kToS h_factor (fibreProduct p q) w0).p).obj (dualNumber Λ k) :=
  (tangentComparisonLinearEquiv openImmersion kToS h_factor p q w0).symm.toLinearMap ∘ₗ
    BasedFunctor.connectingLinearMap
      (mapP openImmersion h_factor p q w0) (mapQ openImmersion h_factor p q w0)

/-- `connectingLinearMap` is the comparison transport of `BasedFunctor.connecting`. -/
theorem connectingLinearMap_apply
    (α : Functor.infinitesimalAutomorphisms
        (bundled openImmersion kToS h_factor Y (imageY openImmersion p q w0)).p) :
    connectingLinearMap openImmersion kToS h_factor p q w0 α =
      (tangentComparisonLinearEquiv openImmersion kToS h_factor p q w0).symm
        (BasedFunctor.connecting
          (mapP openImmersion h_factor p q w0) (mapQ openImmersion h_factor p q w0) α) :=
  sorry

/-- The differential `Tℱ_{W, k, w0} ⟶ Tℱ_{X, k, x0} × Tℱ_{Z, k, z0}` of the two
projections of `W`. -/
def tangentProdLinearMap :
    (Functor.fiberIsoClassFunctor
          (bundled openImmersion kToS h_factor (fibreProduct p q) w0).p).obj (dualNumber Λ k) →ₗ[k]
      (Functor.fiberIsoClassFunctor
            (bundled openImmersion kToS h_factor X
              (imageX openImmersion p q w0)).p).obj (dualNumber Λ k) ×
        (Functor.fiberIsoClassFunctor
            (bundled openImmersion kToS h_factor Z
              (imageZ openImmersion p q w0)).p).obj (dualNumber Λ k) :=
  LinearMap.prod
    (BasedFunctor.differentialLinearMap
      (CofiberedCategoryOver.Groupoids.toOfFunctor
        (mapFst openImmersion h_factor p q w0)))
    (BasedFunctor.differentialLinearMap
      (CofiberedCategoryOver.Groupoids.toOfFunctor
        (mapSnd openImmersion h_factor p q w0)))

/-- `tangentProdLinearMap` is the pair of differentials of the two projections. -/
theorem tangentProdLinearMap_apply
    (x : (Functor.fiberIsoClassFunctor
        (bundled openImmersion kToS h_factor (fibreProduct p q) w0).p).obj (dualNumber Λ k)) :
    tangentProdLinearMap openImmersion kToS h_factor p q w0 x =
      (BasedFunctor.differential
        (CofiberedCategoryOver.Groupoids.toOfFunctor
          (mapFst openImmersion h_factor p q w0)) x,
        BasedFunctor.differential
          (CofiberedCategoryOver.Groupoids.toOfFunctor
            (mapSnd openImmersion h_factor p q w0)) x) :=
  sorry

/-- The difference of differentials `Tℱ_{X, k, x0} × Tℱ_{Z, k, z0} ⟶ Tℱ_{Y, k, y0}`,
sending `(y, z)` to `dp(y) - dq(z)`. -/
def tangentDiffLinearMap :
    (Functor.fiberIsoClassFunctor
          (bundled openImmersion kToS h_factor X
            (imageX openImmersion p q w0)).p).obj (dualNumber Λ k) ×
        (Functor.fiberIsoClassFunctor
          (bundled openImmersion kToS h_factor Z
            (imageZ openImmersion p q w0)).p).obj (dualNumber Λ k) →ₗ[k]
      (Functor.fiberIsoClassFunctor
          (bundled openImmersion kToS h_factor Y
            (imageY openImmersion p q w0)).p).obj (dualNumber Λ k) :=
  LinearMap.coprod
    (BasedFunctor.differentialLinearMap
      (CofiberedCategoryOver.Groupoids.toOfFunctor
        (mapP openImmersion h_factor p q w0)))
    (-BasedFunctor.differentialLinearMap
      (CofiberedCategoryOver.Groupoids.toOfFunctor
        (mapQ openImmersion h_factor p q w0)))

/-- `tangentDiffLinearMap` evaluates as `dp(y) - dq(z)`. -/
theorem tangentDiffLinearMap_apply
    (y : (Functor.fiberIsoClassFunctor
        (bundled openImmersion kToS h_factor X
          (imageX openImmersion p q w0)).p).obj (dualNumber Λ k))
    (z : (Functor.fiberIsoClassFunctor
        (bundled openImmersion kToS h_factor Z
          (imageZ openImmersion p q w0)).p).obj (dualNumber Λ k)) :
    tangentDiffLinearMap openImmersion kToS h_factor p q w0 (y, z) =
      BasedFunctor.differential
          (CofiberedCategoryOver.Groupoids.toOfFunctor
            (mapP openImmersion h_factor p q w0)) y -
        BasedFunctor.differential
          (CofiberedCategoryOver.Groupoids.toOfFunctor
            (mapQ openImmersion h_factor p q w0)) z :=
  sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
