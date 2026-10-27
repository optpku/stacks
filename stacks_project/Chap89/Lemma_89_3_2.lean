/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsoOverClosedPoints.ExcisionProperties
import StacksCheckRecall

/-!
# Transport of morphism properties across family excision

In the setup of 89.3.0.1, a morphism `f : Y ⟶ X` that is an isomorphism
over `X \ {x i}` is quasi-compact, quasi-separated, separated, locally of
finite presentation, of finite presentation, locally of finite type, of
finite type, proper, integral, or finite if and only if every corresponding
base change `g i : Y i ⟶ U i` is.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

/- Lemma 89.3.2: quasi-compact morphisms correspond under finite-family excision. -/
@[stacks 0BHC] #check (AlgebraicGeometry.AlgebraicSpace.IsoOverClosedPoints.quasiCompact_hom_iff :
    ∀ {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U)
    (Y : IsoOverClosedPoints X x hx),
    QuasiCompact Y.obj.hom ↔
      ∀ i, QuasiCompact (overPullbackSnd (U i).hom Y.obj))

/- Lemma 89.3.2: quasi-separated morphisms correspond under finite-family excision. -/
@[stacks 0BHC] #check (AlgebraicGeometry.AlgebraicSpace.IsoOverClosedPoints.quasiSeparated_hom_iff :
    ∀ {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U)
    (Y : IsoOverClosedPoints X x hx),
    QuasiSeparated Y.obj.hom ↔
      ∀ i, QuasiSeparated (overPullbackSnd (U i).hom Y.obj))

/- Lemma 89.3.2: separated morphisms correspond under finite-family excision. -/
@[stacks 0BHC] #check (AlgebraicGeometry.AlgebraicSpace.IsoOverClosedPoints.separated_hom_iff :
    ∀ {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U)
    (Y : IsoOverClosedPoints X x hx),
    Separated Y.obj.hom ↔
      ∀ i, Separated (overPullbackSnd (U i).hom Y.obj))

/- Lemma 89.3.2: locally of finite presentation morphisms correspond under finite-family excision. -/
@[stacks 0BHC] #check (AlgebraicGeometry.AlgebraicSpace.IsoOverClosedPoints.locallyOfFinitePresentation_hom_iff :
    ∀ {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U)
    (Y : IsoOverClosedPoints X x hx),
    LocallyOfFinitePresentation Y.obj.hom ↔
      ∀ i, LocallyOfFinitePresentation (overPullbackSnd (U i).hom Y.obj))

/- Lemma 89.3.2: of finite presentation morphisms correspond under finite-family excision. -/
@[stacks 0BHC] #check (AlgebraicGeometry.AlgebraicSpace.IsoOverClosedPoints.finitePresentation_hom_iff :
    ∀ {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U)
    (Y : IsoOverClosedPoints X x hx),
    FinitePresentation Y.obj.hom ↔
      ∀ i, FinitePresentation (overPullbackSnd (U i).hom Y.obj))

/- Lemma 89.3.2: locally of finite type morphisms correspond under finite-family excision. -/
@[stacks 0BHC] #check (AlgebraicGeometry.AlgebraicSpace.IsoOverClosedPoints.locallyOfFiniteType_hom_iff :
    ∀ {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U)
    (Y : IsoOverClosedPoints X x hx),
    LocallyOfFiniteType Y.obj.hom ↔
      ∀ i, LocallyOfFiniteType (overPullbackSnd (U i).hom Y.obj))

/- Lemma 89.3.2: of finite type morphisms correspond under finite-family excision. -/
@[stacks 0BHC] #check (AlgebraicGeometry.AlgebraicSpace.IsoOverClosedPoints.finiteType_hom_iff :
    ∀ {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U)
    (Y : IsoOverClosedPoints X x hx),
    FiniteType Y.obj.hom ↔
      ∀ i, FiniteType (overPullbackSnd (U i).hom Y.obj))

/- Lemma 89.3.2: proper morphisms correspond under finite-family excision. -/
@[stacks 0BHC] #check (AlgebraicGeometry.AlgebraicSpace.IsoOverClosedPoints.proper_hom_iff :
    ∀ {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U)
    (Y : IsoOverClosedPoints X x hx),
    Proper Y.obj.hom ↔
      ∀ i, Proper (overPullbackSnd (U i).hom Y.obj))

/- Lemma 89.3.2: integral morphisms correspond under finite-family excision. -/
@[stacks 0BHC] #check (AlgebraicGeometry.AlgebraicSpace.IsoOverClosedPoints.isIntegralHom_hom_iff :
    ∀ {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U)
    (Y : IsoOverClosedPoints X x hx),
    IsIntegralHom Y.obj.hom ↔
      ∀ i, IsIntegralHom (overPullbackSnd (U i).hom Y.obj))

/- Lemma 89.3.2: finite morphisms correspond under finite-family excision. -/
@[stacks 0BHC] #check (AlgebraicGeometry.AlgebraicSpace.IsoOverClosedPoints.isFinite_hom_iff :
    ∀ {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U)
    (Y : IsoOverClosedPoints X x hx),
    IsFinite Y.obj.hom ↔
      ∀ i, IsFinite (overPullbackSnd (U i).hom Y.obj))
