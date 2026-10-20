/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Prod
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.TwoFibreProduct
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Deformation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.RimSchlessinger.TwoFibreProduct
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory.ExactSequence

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

variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
variable (p : X ⟶ Y) (q : Z ⟶ Y)
variable [HasRimSchlessinger X] [HasRimSchlessinger Y] [HasRimSchlessinger Z]
variable (w0 : (FiberedCategoryOver.Groupoids.p (TwoFibreProduct.apex.{u + 1, u, u + 1, u} p q)).Fiber (Over.mk kToS))

/-- The projection of a bundled predeformation category is a deformation category
whenever the category fibred in groupoids satisfies the Rim-Schlessinger condition. -/
instance instIsDeformationCategory_bundled (W : GroupoidsOver S) [HasRimSchlessinger W]
    (w : W.p.Fiber (Over.mk kToS)) :
    Functor.IsDeformationCategory (bundled openImmersion kToS h_factor W w).p :=
  inferInstanceAs
    (Functor.IsDeformationCategory (predeformationFunctor W openImmersion kToS h_factor w))

/-- The canonical comparison from the predeformation category of a two-fibre product
to the two-fibre product of predeformation categories induces a bijection on tangent spaces. -/
theorem bijective_differential_fibreProductComparison :
    Function.Bijective
      (BasedFunctor.differentialLinearMap
        (CofiberedCategoryOver.Groupoids.toBasedFunctor
          (comparison openImmersion kToS h_factor p q
            (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q)
            (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q)
            (TwoFibreProduct.comparisonIso p q) w0))) :=
  sorry

/-- The canonical comparison identifies the tangent space of the predeformation
category of a two-fibre product with that of the two-fibre product of predeformation categories. -/
def tangentComparisonLinearEquiv :
    (Functor.fiberIsoClassFunctor
          (bundled openImmersion kToS h_factor (TwoFibreProduct.apex.{u + 1, u, u + 1, u} p q) w0).p).obj
        (dualNumber Λ k) ≃ₗ[k]
      (Functor.fiberIsoClassFunctor
          (CofiberedCategoryOver.Groupoids.p (TwoFibreProduct.apex.{u + 1, u, u + 1, u}
            (mapBundled openImmersion kToS h_factor p (residueImage (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) w0))
            (mapAlong openImmersion kToS h_factor q
              (residueIso kToS p q (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q)
                (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q) (TwoFibreProduct.comparisonIso p q) w0))))).obj (dualNumber Λ k) :=
  LinearEquiv.ofBijective
    (BasedFunctor.differentialLinearMap
      (CofiberedCategoryOver.Groupoids.toBasedFunctor
        (comparison openImmersion kToS h_factor p q
          (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q)
          (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q)
          (TwoFibreProduct.comparisonIso p q) w0)))
    (bijective_differential_fibreProductComparison openImmersion kToS h_factor p q w0)

/-- The tangent comparison equivalence acts by the differential of the canonical
comparison of predeformation categories. -/
theorem tangentComparisonLinearEquiv_apply
    (x : (Functor.fiberIsoClassFunctor
        (bundled openImmersion kToS h_factor (TwoFibreProduct.apex.{u + 1, u, u + 1, u} p q) w0).p).obj (dualNumber Λ k)) :
    tangentComparisonLinearEquiv openImmersion kToS h_factor p q w0 x =
      BasedFunctor.differential
        (CofiberedCategoryOver.Groupoids.toBasedFunctor
          (comparison openImmersion kToS h_factor p q
            (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q)
            (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q)
            (TwoFibreProduct.comparisonIso p q) w0)) x :=
  sorry

/-- The map `Inf(ℱ_{W, k, w0}) ⟶ Inf(ℱ_{X, k, x0}) × Inf(ℱ_{Z, k, z0})` induced by the
two projections of `W`. -/
def infProdLinearMap :
    Functor.infinitesimalAutomorphisms
        (bundled openImmersion kToS h_factor (TwoFibreProduct.apex.{u + 1, u, u + 1, u} p q) w0).p →ₗ[k]
      Functor.infinitesimalAutomorphisms
          (bundled openImmersion kToS h_factor X (residueImage (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) w0)).p ×
        Functor.infinitesimalAutomorphisms
          (bundled openImmersion kToS h_factor Z (residueImage (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q) w0)).p :=
  LinearMap.prod
    (BasedFunctor.mapInfinitesimalAutomorphismsLinearMap
      (CofiberedCategoryOver.Groupoids.toBasedFunctor
        (mapBundled openImmersion kToS h_factor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) w0)))
    (BasedFunctor.mapInfinitesimalAutomorphismsLinearMap
      (CofiberedCategoryOver.Groupoids.toBasedFunctor
        (mapBundled openImmersion kToS h_factor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q) w0)))

/-- `infProdLinearMap` is the pair of unpointed infinitesimal maps of the two projections. -/
theorem infProdLinearMap_apply
    (α : Functor.infinitesimalAutomorphisms
        (bundled openImmersion kToS h_factor (TwoFibreProduct.apex.{u + 1, u, u + 1, u} p q) w0).p) :
    infProdLinearMap openImmersion kToS h_factor p q w0 α =
      (BasedFunctor.mapInfinitesimalAutomorphisms
        (CofiberedCategoryOver.Groupoids.toBasedFunctor
          (mapBundled openImmersion kToS h_factor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) w0)) α,
        BasedFunctor.mapInfinitesimalAutomorphisms
          (CofiberedCategoryOver.Groupoids.toBasedFunctor
            (mapBundled openImmersion kToS h_factor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q) w0)) α) :=
  sorry

/-- The difference map `Inf(ℱ_{X, k, x0}) × Inf(ℱ_{Z, k, z0}) ⟶ Inf(ℱ_{Y, k, y0})`,
sending `(β, γ)` to `Inf(p)(β) - Inf(q)(γ)`. -/
def infDiffLinearMap :
    Functor.infinitesimalAutomorphisms
          (bundled openImmersion kToS h_factor X (residueImage (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) w0)).p ×
        Functor.infinitesimalAutomorphisms
          (bundled openImmersion kToS h_factor Z (residueImage (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q) w0)).p →ₗ[k]
      Functor.infinitesimalAutomorphisms
        (bundled openImmersion kToS h_factor Y (residueImage p (residueImage (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) w0))).p :=
  LinearMap.coprod
    (BasedFunctor.mapInfinitesimalAutomorphismsLinearMap
      (CofiberedCategoryOver.Groupoids.toBasedFunctor
        (mapBundled openImmersion kToS h_factor p (residueImage (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) w0))))
    (-BasedFunctor.mapInfinitesimalAutomorphismsLinearMap
      (CofiberedCategoryOver.Groupoids.toBasedFunctor
        (mapAlong openImmersion kToS h_factor q
          (residueIso kToS p q (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q)
            (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q) (TwoFibreProduct.comparisonIso p q) w0))))

/-- `infDiffLinearMap` evaluates as `Inf(p)(β) - Inf(q)(γ)`. -/
theorem infDiffLinearMap_apply
    (β : Functor.infinitesimalAutomorphisms
        (bundled openImmersion kToS h_factor X (residueImage (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) w0)).p)
    (γ : Functor.infinitesimalAutomorphisms
        (bundled openImmersion kToS h_factor Z (residueImage (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q) w0)).p) :
    infDiffLinearMap openImmersion kToS h_factor p q w0 (β, γ) =
      BasedFunctor.mapInfinitesimalAutomorphisms
          (CofiberedCategoryOver.Groupoids.toBasedFunctor
            (mapBundled openImmersion kToS h_factor p (residueImage (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) w0))) β -
        BasedFunctor.mapInfinitesimalAutomorphisms
          (CofiberedCategoryOver.Groupoids.toBasedFunctor
            (mapAlong openImmersion kToS h_factor q
              (residueIso kToS p q (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q)
                (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q) (TwoFibreProduct.comparisonIso p q) w0))) γ :=
  sorry

/-- The boundary from infinitesimal automorphisms of the common image to tangent
vectors of the two-fibre product, transported through the inverse tangent comparison. -/
def connectingLinearMap :
    Functor.infinitesimalAutomorphisms
        (bundled openImmersion kToS h_factor Y (residueImage p (residueImage (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) w0))).p →ₗ[k]
      (Functor.fiberIsoClassFunctor
          (bundled openImmersion kToS h_factor (TwoFibreProduct.apex.{u + 1, u, u + 1, u} p q) w0).p).obj (dualNumber Λ k) :=
  (tangentComparisonLinearEquiv openImmersion kToS h_factor p q w0).symm.toLinearMap ∘ₗ
    BasedFunctor.connectingLinearMap
      (mapBundled openImmersion kToS h_factor p (residueImage (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) w0)) (mapAlong openImmersion kToS h_factor q
        (residueIso kToS p q (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q)
          (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q) (TwoFibreProduct.comparisonIso p q) w0))

/-- `connectingLinearMap` is the comparison transport of `BasedFunctor.connecting`. -/
theorem connectingLinearMap_apply
    (α : Functor.infinitesimalAutomorphisms
        (bundled openImmersion kToS h_factor Y (residueImage p (residueImage (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) w0))).p) :
    connectingLinearMap openImmersion kToS h_factor p q w0 α =
      (tangentComparisonLinearEquiv openImmersion kToS h_factor p q w0).symm
        (BasedFunctor.connecting
          (mapBundled openImmersion kToS h_factor p (residueImage (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) w0)) (mapAlong openImmersion kToS h_factor q
            (residueIso kToS p q (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q)
              (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q) (TwoFibreProduct.comparisonIso p q) w0)) α) :=
  sorry

/-- The differential `Tℱ_{W, k, w0} ⟶ Tℱ_{X, k, x0} × Tℱ_{Z, k, z0}` of the two
projections of `W`. -/
def tangentProdLinearMap :
    (Functor.fiberIsoClassFunctor
          (bundled openImmersion kToS h_factor (TwoFibreProduct.apex.{u + 1, u, u + 1, u} p q) w0).p).obj (dualNumber Λ k) →ₗ[k]
      (Functor.fiberIsoClassFunctor
            (bundled openImmersion kToS h_factor X
              (residueImage (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) w0)).p).obj (dualNumber Λ k) ×
        (Functor.fiberIsoClassFunctor
            (bundled openImmersion kToS h_factor Z
              (residueImage (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q) w0)).p).obj (dualNumber Λ k) :=
  LinearMap.prod
    (BasedFunctor.differentialLinearMap
      (CofiberedCategoryOver.Groupoids.toBasedFunctor
        (mapBundled openImmersion kToS h_factor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) w0)))
    (BasedFunctor.differentialLinearMap
      (CofiberedCategoryOver.Groupoids.toBasedFunctor
        (mapBundled openImmersion kToS h_factor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q) w0)))

/-- `tangentProdLinearMap` is the pair of differentials of the two projections. -/
theorem tangentProdLinearMap_apply
    (x : (Functor.fiberIsoClassFunctor
        (bundled openImmersion kToS h_factor (TwoFibreProduct.apex.{u + 1, u, u + 1, u} p q) w0).p).obj (dualNumber Λ k)) :
    tangentProdLinearMap openImmersion kToS h_factor p q w0 x =
      (BasedFunctor.differential
        (CofiberedCategoryOver.Groupoids.toBasedFunctor
          (mapBundled openImmersion kToS h_factor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) w0)) x,
        BasedFunctor.differential
          (CofiberedCategoryOver.Groupoids.toBasedFunctor
            (mapBundled openImmersion kToS h_factor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q) w0)) x) :=
  sorry

/-- The difference of differentials `Tℱ_{X, k, x0} × Tℱ_{Z, k, z0} ⟶ Tℱ_{Y, k, y0}`,
sending `(y, z)` to `dp(y) - dq(z)`. -/
def tangentDiffLinearMap :
    (Functor.fiberIsoClassFunctor
          (bundled openImmersion kToS h_factor X
            (residueImage (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) w0)).p).obj (dualNumber Λ k) ×
        (Functor.fiberIsoClassFunctor
          (bundled openImmersion kToS h_factor Z
            (residueImage (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q) w0)).p).obj (dualNumber Λ k) →ₗ[k]
      (Functor.fiberIsoClassFunctor
          (bundled openImmersion kToS h_factor Y
            (residueImage p (residueImage (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) w0))).p).obj (dualNumber Λ k) :=
  LinearMap.coprod
    (BasedFunctor.differentialLinearMap
      (CofiberedCategoryOver.Groupoids.toBasedFunctor
        (mapBundled openImmersion kToS h_factor p (residueImage (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) w0))))
    (-BasedFunctor.differentialLinearMap
      (CofiberedCategoryOver.Groupoids.toBasedFunctor
        (mapAlong openImmersion kToS h_factor q
          (residueIso kToS p q (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q)
            (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q) (TwoFibreProduct.comparisonIso p q) w0))))

/-- `tangentDiffLinearMap` evaluates as `dp(y) - dq(z)`. -/
theorem tangentDiffLinearMap_apply
    (y : (Functor.fiberIsoClassFunctor
        (bundled openImmersion kToS h_factor X
          (residueImage (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) w0)).p).obj (dualNumber Λ k))
    (z : (Functor.fiberIsoClassFunctor
        (bundled openImmersion kToS h_factor Z
          (residueImage (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q) w0)).p).obj (dualNumber Λ k)) :
    tangentDiffLinearMap openImmersion kToS h_factor p q w0 (y, z) =
      Sub.sub
        (α := (Functor.fiberIsoClassFunctor
          (bundled openImmersion kToS h_factor Y
            (residueImage p (residueImage (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) w0))).p).obj (dualNumber Λ k))
        (BasedFunctor.differential
          (CofiberedCategoryOver.Groupoids.toBasedFunctor
            (mapBundled openImmersion kToS h_factor p (residueImage (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q) w0))) y)
        (BasedFunctor.differential
          (CofiberedCategoryOver.Groupoids.toBasedFunctor
            (mapAlong openImmersion kToS h_factor q
              (residueIso kToS p q (TwoFibreProduct.fst.{u + 1, u, u + 1, u} p q)
                (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q) (TwoFibreProduct.comparisonIso p q) w0))) z) :=
  sorry

/-- The infinitesimal automorphism and tangent spaces at a residue object of a
two-fibre product of Rim-Schlessinger categories fibred in groupoids form a
six-term exact sequence: the first projection map is injective, and every
consecutive pair of the five canonical linear maps is exact. -/
theorem infTangentSequence_exact :
    Function.Injective (infProdLinearMap openImmersion kToS h_factor p q w0) ∧
      Function.Exact (infProdLinearMap openImmersion kToS h_factor p q w0)
        (infDiffLinearMap openImmersion kToS h_factor p q w0) ∧
      Function.Exact (infDiffLinearMap openImmersion kToS h_factor p q w0)
        (connectingLinearMap openImmersion kToS h_factor p q w0) ∧
      Function.Exact (connectingLinearMap openImmersion kToS h_factor p q w0)
        (tangentProdLinearMap openImmersion kToS h_factor p q w0) ∧
      Function.Exact (tangentProdLinearMap openImmersion kToS h_factor p q w0)
        (tangentDiffLinearMap openImmersion kToS h_factor p q w0) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
