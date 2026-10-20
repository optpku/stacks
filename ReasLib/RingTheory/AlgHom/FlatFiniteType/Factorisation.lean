/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.AlgHom.Factorisation

@[expose] public section

/-!
# Flat finite-type factorisations of algebra homomorphisms

This file attaches flatness and finite type to the source leg of the
arbitrary-universe factorisation owner `AlgHom.Factorisation.Through`.
Properties are stored on the algebra map, so the construction does not create
a second algebra structure on the midpoint.
-/

universe u v w x

namespace AlgHom.Factorisation

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable {f : A →ₐ[R] B}

/-- An arbitrary-universe factorisation whose source leg is flat and of
finite type. -/
@[stacks 0BJ2 "flat finite-type algebra-map factorisation"]
structure FlatFiniteType (f : A →ₐ[R] B) where
  /-- The intermediate algebra. -/
  mid : Type x
  /-- The commutative-ring structure on the intermediate algebra. -/
  instCommRing : CommRing mid
  /-- The base-algebra structure on the intermediate algebra. -/
  instAlgebra : Algebra R mid
  /-- The underlying arbitrary-universe triangle. -/
  base : Through f mid
  /-- The source leg is flat. -/
  flat : base.fromSource.toRingHom.Flat
  /-- The source leg is of finite type. -/
  finiteType : base.fromSource.FiniteType

attribute [instance] FlatFiniteType.instCommRing FlatFiniteType.instAlgebra

namespace FlatFiniteType

/-- Attach flatness and finite type to an existing arbitrary-universe
factorisation. -/
def of {M : Type x} [CommRing M] [Algebra R M] (F : Through f M)
    (flat : F.fromSource.toRingHom.Flat)
    (finiteType : F.fromSource.FiniteType) : FlatFiniteType.{u, v, w, x} f where
  mid := M
  instCommRing := inferInstance
  instAlgebra := inferInstance
  base := F
  flat := flat
  finiteType := finiteType

/-- Build a flat finite-type factorisation directly from its two maps and
their mathematical properties. -/
def ofMaps {M : Type x} [CommRing M] [Algebra R M]
    (fromSource : A →ₐ[R] M) (toTarget : M →ₐ[R] B)
    (factor : toTarget.comp fromSource = f)
    (flat : fromSource.toRingHom.Flat) (finiteType : fromSource.FiniteType) :
    FlatFiniteType.{u, v, w, x} f :=
  FlatFiniteType.of (Through.ofMaps fromSource toTarget factor) flat finiteType

/-- The source map of a flat finite-type factorisation. -/
abbrev fromSource (F : FlatFiniteType.{u, v, w, x} f) : A →ₐ[R] F.mid :=
  F.base.fromSource

/-- The target map of a flat finite-type factorisation. -/
abbrev toTarget (F : FlatFiniteType.{u, v, w, x} f) : F.mid →ₐ[R] B :=
  F.base.toTarget

/-- The triangle equation carried by a flat finite-type factorisation. -/
theorem factor (F : FlatFiniteType.{u, v, w, x} f) :
    F.toTarget.comp F.fromSource = f := sorry

/-- The flatness, finite-type, and triangle laws carried by a flat
finite-type factorisation. -/
theorem spec (F : FlatFiniteType.{u, v, w, x} f) :
    F.fromSource.toRingHom.Flat ∧ F.fromSource.FiniteType ∧
      F.toTarget.comp F.fromSource = f := sorry

/-- The underlying triangle supplied to `FlatFiniteType.of` is recovered by
projection. -/
@[simp]
theorem base_of {M : Type x} [CommRing M] [Algebra R M] (F : Through f M)
    (flat : F.fromSource.toRingHom.Flat) (finiteType : F.fromSource.FiniteType) :
    (FlatFiniteType.of F flat finiteType).base = F := sorry

/-- The source map supplied to `FlatFiniteType.ofMaps` is recovered by
projection. -/
@[simp]
theorem fromSource_ofMaps {M : Type x} [CommRing M] [Algebra R M]
    (fromSource : A →ₐ[R] M) (toTarget : M →ₐ[R] B)
    (factor : toTarget.comp fromSource = f)
    (flat : fromSource.toRingHom.Flat) (finiteType : fromSource.FiniteType) :
    (FlatFiniteType.ofMaps fromSource toTarget factor flat finiteType).fromSource =
      fromSource := sorry

/-- The target map supplied to `FlatFiniteType.ofMaps` is recovered by
projection. -/
@[simp]
theorem toTarget_ofMaps {M : Type x} [CommRing M] [Algebra R M]
    (fromSource : A →ₐ[R] M) (toTarget : M →ₐ[R] B)
    (factor : toTarget.comp fromSource = f)
    (flat : fromSource.toRingHom.Flat) (finiteType : fromSource.FiniteType) :
    (FlatFiniteType.ofMaps fromSource toTarget factor flat finiteType).toTarget =
      toTarget := sorry

section OfId

variable {T : Type w} [CommRing T] [Algebra R T]

/-- For a factorisation of the structural map, the source leg is the
structural map to its midpoint. -/
@[simp]
theorem fromSource_toRingHom_ofId
    (F : FlatFiniteType.{u, u, w, x} (Algebra.ofId R T)) :
    F.fromSource.toRingHom = algebraMap R F.mid := sorry

/-- A flat finite-type factorisation of a structural map exposes canonical
module flatness on its midpoint. -/
instance instFlatOfId
    (F : FlatFiniteType.{u, u, w, x} (Algebra.ofId R T)) :
    Module.Flat R F.mid := sorry

/-- A flat finite-type factorisation of a structural map exposes canonical
finite type on its midpoint. -/
instance instFiniteTypeOfId
    (F : FlatFiniteType.{u, u, w, x} (Algebra.ofId R T)) :
    Algebra.FiniteType R F.mid := sorry

/-- Composing an algebra map with the structural map gives the structural
map to its target. -/
theorem ofId_factor {M : Type x} [CommRing M] [Algebra R M]
    (toTarget : M →ₐ[R] T) :
    toTarget.comp (Algebra.ofId R M) = Algebra.ofId R T := sorry

/-- The structural map of a flat algebra is flat as a ring homomorphism. -/
theorem ofId_flat {M : Type x} [CommRing M] [Algebra R M] [Module.Flat R M] :
    (Algebra.ofId R M).toRingHom.Flat := sorry

/-- The structural map of a finite-type algebra is a finite-type algebra
homomorphism. -/
theorem ofId_finiteType {M : Type x} [CommRing M] [Algebra R M]
    [Algebra.FiniteType R M] :
    (Algebra.ofId R M).FiniteType := sorry

/-- Build a flat finite-type factorisation of a structural map from its
midpoint and target map. -/
def ofId {M : Type x} [CommRing M] [Algebra R M] [Module.Flat R M]
    [Algebra.FiniteType R M] (toTarget : M →ₐ[R] T) :
    FlatFiniteType.{u, u, w, x} (Algebra.ofId R T) :=
  FlatFiniteType.ofMaps (Algebra.ofId R M) toTarget (ofId_factor toTarget)
    ofId_flat ofId_finiteType

/-- The midpoint supplied to `FlatFiniteType.ofId` is recovered by
projection. -/
@[simp]
theorem mid_ofId {M : Type x} [CommRing M] [Algebra R M] [Module.Flat R M]
    [Algebra.FiniteType R M] (toTarget : M →ₐ[R] T) :
    (FlatFiniteType.ofId toTarget).mid = M := sorry

/-- The source map of `FlatFiniteType.ofId` is the structural map. -/
@[simp]
theorem fromSource_ofId {M : Type x} [CommRing M] [Algebra R M]
    [Module.Flat R M] [Algebra.FiniteType R M] (toTarget : M →ₐ[R] T) :
    (FlatFiniteType.ofId toTarget).fromSource = Algebra.ofId R M := sorry

/-- The target map supplied to `FlatFiniteType.ofId` is recovered by
projection. -/
@[simp]
theorem toTarget_ofId {M : Type x} [CommRing M] [Algebra R M]
    [Module.Flat R M] [Algebra.FiniteType R M] (toTarget : M →ₐ[R] T) :
    (FlatFiniteType.ofId toTarget).toTarget = toTarget := sorry

end OfId

end FlatFiniteType

end AlgHom.Factorisation
