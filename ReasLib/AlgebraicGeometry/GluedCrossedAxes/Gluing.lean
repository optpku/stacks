/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.AlgebraicGeometry.GluedCrossedAxes.CoordinateRing
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Gluing two affine crossed axes

Coordinate inversion identifies the punctured axes of two affine charts.
Their pushout is a separated scheme of finite type over the field, with two
distinct rational origins and a canonical structure morphism.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GluedCrossedAxes

/-- The affine crossed axes `Spec (k[x, y] / (x * y))`. -/
def crossedAxes (k : Type u) [Field k] : Scheme.{u} :=
  Spec (.of (CoordinateRing k))

/-- The overlap scheme `Spec(C)`. -/
def overlap (k : Type u) [Field k] : Scheme.{u} :=
  Spec (.of (OverlapRing k))

/-- The open immersion `Spec(C) ⟶ Spec(A)` induced by `fromA`. -/
def mapA (k : Type u) [Field k] : overlap k ⟶ crossedAxes k :=
  Spec.map (CommRingCat.ofHom (fromA k).toRingHom)

/-- The open immersion `Spec(C) ⟶ Spec(B)` induced by `fromB`. -/
def mapB (k : Type u) [Field k] : overlap k ⟶ crossedAxes k :=
  Spec.map (CommRingCat.ofHom (fromB k).toRingHom)

/-- `Spec.map fromA` is an open immersion, since it identifies `Spec(C)` with `D(x + y)`. -/
instance mapA_isOpenImmersion (k : Type u) [Field k] :
    IsOpenImmersion (mapA k) := sorry

/-- `Spec.map fromB` is an open immersion, since it identifies `Spec(C)` with `D(u + v)`. -/
instance mapB_isOpenImmersion (k : Type u) [Field k] :
    IsOpenImmersion (mapB k) := sorry

/-- The glued scheme `X = Spec(A) ⨿_{Spec(C)} Spec(B)`. -/
def scheme (k : Type u) [Field k] : Scheme.{u} :=
  pushout (mapA k) (mapB k)

/-- The open immersion of the first affine chart `Spec(A) ⊂ X`. -/
def chartA (k : Type u) [Field k] : crossedAxes k ⟶ scheme k :=
  pushout.inl (mapA k) (mapB k)

/-- The open immersion of the second affine chart `Spec(B) ⊂ X`. -/
def chartB (k : Type u) [Field k] : crossedAxes k ⟶ scheme k :=
  pushout.inr (mapA k) (mapB k)

/-- The first chart inclusion is an open immersion. -/
instance chartA_isOpenImmersion (k : Type u) [Field k] :
    IsOpenImmersion (chartA k) := sorry

/-- The second chart inclusion is an open immersion. -/
instance chartB_isOpenImmersion (k : Type u) [Field k] :
    IsOpenImmersion (chartB k) := sorry

/-- The two charts overlap exactly along the image of `Spec(C)`. -/
theorem overlap_isPullback (k : Type u) [Field k] :
    IsPullback (mapA k) (mapB k) (chartA k) (chartB k) := sorry

/-- The structure morphism of one affine chart to `Spec k`. -/
def crossedAxesToBase (k : Type u) [Field k] :
    crossedAxes k ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (CoordinateRing k)))

/-- The two chart structure morphisms agree after restriction from `Spec(C)`. -/
private theorem toBase_compat (k : Type u) [Field k] :
    mapA k ≫ crossedAxesToBase k = mapB k ≫ crossedAxesToBase k := sorry

/-- The structure morphism `X ⟶ Spec k`. -/
@[no_expose]
def toBase (k : Type u) [Field k] : scheme k ⟶ Spec (.of k) :=
  pushout.desc (crossedAxesToBase k) (crossedAxesToBase k) (toBase_compat k)

/-- The first chart commutes with the structure morphisms to `Spec k`. -/
theorem chartA_comp_toBase (k : Type u) [Field k] :
    chartA k ≫ toBase k = crossedAxesToBase k := sorry

/-- The second chart commutes with the structure morphisms to `Spec k`. -/
theorem chartB_comp_toBase (k : Type u) [Field k] :
    chartB k ≫ toBase k = crossedAxesToBase k := sorry

/-- The `k`-rational origin of the affine crossed axes, as a morphism `Spec k ⟶ Spec(A)`. -/
def crossedAxesOriginSection (k : Type u) [Field k] :
    Spec (.of k) ⟶ crossedAxes k :=
  Spec.map (CommRingCat.ofHom (originEval k).toRingHom)

/-- The origin of the first chart, as a morphism `Spec k ⟶ X`. -/
def originASection (k : Type u) [Field k] : Spec (.of k) ⟶ scheme k :=
  crossedAxesOriginSection k ≫ chartA k

/-- The origin of the second chart, as a morphism `Spec k ⟶ X`. -/
def originBSection (k : Type u) [Field k] : Spec (.of k) ⟶ scheme k :=
  crossedAxesOriginSection k ≫ chartB k

/-- The `k`-rational origin of the first affine chart, viewed as a point of `X`. -/
def originA (k : Type u) [Field k] : scheme k :=
  (originASection k).base (IsLocalRing.closedPoint k)

/-- The `k`-rational origin of the second affine chart, viewed as a point of `X`. -/
def originB (k : Type u) [Field k] : scheme k :=
  (originBSection k).base (IsLocalRing.closedPoint k)

/-- The two chart origins are distinct points of `X`. -/
theorem originA_ne_originB (k : Type u) [Field k] :
    originA k ≠ originB k := sorry

/-- the glued scheme `X` is separated over `k`. -/
instance toBase_isSeparated (k : Type u) [Field k] :
    IsSeparated (toBase k) := sorry

/-- The glued scheme is a separated scheme. -/
instance scheme_isSeparated (k : Type u) [Field k] :
    (scheme k).IsSeparated := sorry

/-- the glued scheme `X` is of finite type over `k`. -/
instance toBase_finiteType (k : Type u) [Field k] :
    Scheme.Hom.FiniteType (toBase k) := sorry

end AlgebraicGeometry.GluedCrossedAxes
