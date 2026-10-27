/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsoOverClosedPoints.Excision
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsoOverOpen.ExcisionProperties

/-! # Morphism properties under finite-family étale excision -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.IsoOverClosedPoints

/-- For a finite family of distinct closed points of a decent algebraic space, with affine
elementary étale neighbourhoods whose inverse images of the family are singletons,
a morphism that is an isomorphism off the family is quasi-compact if and only if
every neighbourhood base change is quasi-compact. -/
theorem quasiCompact_hom_iff {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U)
    (Y : IsoOverClosedPoints X x hx) :
    QuasiCompact Y.obj.hom ↔
      ∀ i, QuasiCompact (overPullbackSnd (U i).hom Y.obj) :=
  sorry

/-- For a finite family of distinct closed points of a decent algebraic space, with affine
elementary étale neighbourhoods whose inverse images of the family are singletons,
a morphism that is an isomorphism off the family is quasi-separated if and only if
every neighbourhood base change is quasi-separated. -/
theorem quasiSeparated_hom_iff {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U)
    (Y : IsoOverClosedPoints X x hx) :
    QuasiSeparated Y.obj.hom ↔
      ∀ i, QuasiSeparated (overPullbackSnd (U i).hom Y.obj) :=
  sorry

/-- For a finite family of distinct closed points of a decent algebraic space, with affine
elementary étale neighbourhoods whose inverse images of the family are singletons,
a morphism that is an isomorphism off the family is separated if and only if
every neighbourhood base change is separated. -/
theorem separated_hom_iff {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U)
    (Y : IsoOverClosedPoints X x hx) :
    Separated Y.obj.hom ↔
      ∀ i, Separated (overPullbackSnd (U i).hom Y.obj) :=
  sorry

/-- For a finite family of distinct closed points of a decent algebraic space, with affine
elementary étale neighbourhoods whose inverse images of the family are singletons,
a morphism that is an isomorphism off the family is locally of finite presentation if and only if
every neighbourhood base change is locally of finite presentation. -/
theorem locallyOfFinitePresentation_hom_iff {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U)
    (Y : IsoOverClosedPoints X x hx) :
    LocallyOfFinitePresentation Y.obj.hom ↔
      ∀ i, LocallyOfFinitePresentation (overPullbackSnd (U i).hom Y.obj) :=
  sorry

/-- For a finite family of distinct closed points of a decent algebraic space, with affine
elementary étale neighbourhoods whose inverse images of the family are singletons,
a morphism that is an isomorphism off the family is of finite presentation if and only if
every neighbourhood base change is of finite presentation. -/
theorem finitePresentation_hom_iff {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U)
    (Y : IsoOverClosedPoints X x hx) :
    FinitePresentation Y.obj.hom ↔
      ∀ i, FinitePresentation (overPullbackSnd (U i).hom Y.obj) :=
  sorry

/-- For a finite family of distinct closed points of a decent algebraic space, with affine
elementary étale neighbourhoods whose inverse images of the family are singletons,
a morphism that is an isomorphism off the family is locally of finite type if and only if
every neighbourhood base change is locally of finite type. -/
theorem locallyOfFiniteType_hom_iff {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U)
    (Y : IsoOverClosedPoints X x hx) :
    LocallyOfFiniteType Y.obj.hom ↔
      ∀ i, LocallyOfFiniteType (overPullbackSnd (U i).hom Y.obj) :=
  sorry

/-- For a finite family of distinct closed points of a decent algebraic space, with affine
elementary étale neighbourhoods whose inverse images of the family are singletons,
a morphism that is an isomorphism off the family is of finite type if and only if
every neighbourhood base change is of finite type. -/
theorem finiteType_hom_iff {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U)
    (Y : IsoOverClosedPoints X x hx) :
    FiniteType Y.obj.hom ↔
      ∀ i, FiniteType (overPullbackSnd (U i).hom Y.obj) :=
  sorry

/-- For a finite family of distinct closed points of a decent algebraic space, with affine
elementary étale neighbourhoods whose inverse images of the family are singletons,
a morphism that is an isomorphism off the family is proper if and only if
every neighbourhood base change is proper. -/
theorem proper_hom_iff {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U)
    (Y : IsoOverClosedPoints X x hx) :
    Proper Y.obj.hom ↔
      ∀ i, Proper (overPullbackSnd (U i).hom Y.obj) :=
  sorry

/-- For a finite family of distinct closed points of a decent algebraic space, with affine
elementary étale neighbourhoods whose inverse images of the family are singletons,
a morphism that is an isomorphism off the family is integral if and only if
every neighbourhood base change is integral. -/
theorem isIntegralHom_hom_iff {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U)
    (Y : IsoOverClosedPoints X x hx) :
    IsIntegralHom Y.obj.hom ↔
      ∀ i, IsIntegralHom (overPullbackSnd (U i).hom Y.obj) :=
  sorry

/-- For a finite family of distinct closed points of a decent algebraic space, with affine
elementary étale neighbourhoods whose inverse images of the family are singletons,
a morphism that is an isomorphism off the family is finite if and only if
every neighbourhood base change is finite. -/
theorem isFinite_hom_iff {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U)
    (Y : IsoOverClosedPoints X x hx) :
    IsFinite Y.obj.hom ↔
      ∀ i, IsFinite (overPullbackSnd (U i).hom Y.obj) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsoOverClosedPoints
