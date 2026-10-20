module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap90.Lemma_90_20_1_LinearMap
public import stacks_project.Chap99.Lemma_99_16_10_Predeformation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-dimensional tangent and infinitesimal automorphism spaces

In Situation 99.16.3, if `S` is locally Noetherian and `toBase B` is locally of
finite presentation, then for every finite-type field `k` over `S` and every
object `x0` of `Complexes f` over `k`, the Artin spaces `Tℱ` and `Inf(ℱ)` of
the associated predeformation functor are finite-dimensional over `k`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Complexes
open ArtinianLocalAlgCat

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

/-- Lemma 99.16.10 (1): in Situation 99.16.3, if `S` is locally Noetherian and
`toBase B` is locally of finite presentation, then for a finite-type field `k`
over `S` and an object `x0` of `Complexes f` over `k`, corresponding to a triple
`(Spec(k), g0, E0)` with `g0 = (fiberInclusion.obj x0).σ.hom` and
`E0 = (fiberInclusion.obj x0).complex`, the Artin tangent space `Tℱ_{X, k, x0}`
is finite-dimensional over `k`. -/
@[stacks 0DLL]
theorem finiteDimensional_tangentSpace
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X B : AlgebraicSpace S}
    (f : X ⟶ B)
    [∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f] [FinitePresentation f]
    [LocallyOfFinitePresentation (toBase B)] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : (p f).Fiber (Over.mk kToS)) :
    FiniteDimensional k (tangentSpace f openImmersion kToS h_factor x0) :=
  sorry

/-- Lemma 99.16.10 (2): in Situation 99.16.3, if `S` is locally Noetherian and
`toBase B` is locally of finite presentation, then for a finite-type field `k`
over `S` and an object `x0` of `Complexes f` over `k`, corresponding to a triple
`(Spec(k), g0, E0)` with `g0 = (fiberInclusion.obj x0).σ.hom` and
`E0 = (fiberInclusion.obj x0).complex`, the infinitesimal automorphism space
`Inf(ℱ_{X, k, x0})` is finite-dimensional over `k`. -/
@[stacks 0DLL]
theorem finiteDimensional_infinitesimalAutomorphisms
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X B : AlgebraicSpace S}
    (f : X ⟶ B)
    [∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f] [FinitePresentation f]
    [LocallyOfFinitePresentation (toBase B)] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : (p f).Fiber (Over.mk kToS)) :
    FiniteDimensional k
      (infinitesimalAutomorphisms f openImmersion kToS h_factor x0) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Complexes
