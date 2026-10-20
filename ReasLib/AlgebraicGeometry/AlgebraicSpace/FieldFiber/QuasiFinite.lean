/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.Locality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite.Locus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions

/-!
# Fibre conditions and quasi-finiteness

For locally finite-type morphisms of algebraic spaces, discreteness and dimension
at most zero of field-valued fibres characterize pointwise quasi-finiteness.
Decency relates these conditions to the topology and finiteness of set-theoretic fibres.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a locally finite-type morphism, discreteness of a field-valued fibre,
topological dimension at most zero, étale-local dimension at most zero, and
quasi-finiteness at every point over its represented point are equivalent. -/
theorem tfae_fieldFiber_discrete_dimension_quasiFiniteAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (p : FieldValuedPoint Y) :
    List.TFAE
      [ DiscreteTopology (Points (fieldFiber f p))
      , topologicalKrullDim (Points (fieldFiber f p)) ≤ 0
      , dimension (fieldFiber f p) ≤ 0
      , ∀ x : Points X, Points.map f x = Points.mk p → QuasiFiniteAt f x ] :=
  sorry

/-- A finite field-valued fibre has a finite set-theoretic fibre over its
represented point, for any morphism of algebraic spaces. -/
theorem finite_fiberOver_of_finite_fieldFiber {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (p : FieldValuedPoint Y) (hXk : Finite (Points (fieldFiber f p))) :
    (fiberOver f (Points.mk p)).Finite :=
  sorry

/-- A finite field-valued fibre of a decent, locally finite-type morphism
has discrete topology. -/
instance discreteTopology_fieldFiber_of_decent_finite {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] [Decent f]
    (p : FieldValuedPoint Y) [Finite (Points (fieldFiber f p))] :
    DiscreteTopology (Points (fieldFiber f p)) :=
  sorry

/-- For a locally finite-type morphism with decent target, discreteness and
topological dimension at most zero of the set-theoretic fibre are equivalent to
discreteness, topological dimension at most zero, and étale-local dimension at
most zero of a field-valued fibre, and to quasi-finiteness above its represented point. -/
theorem tfae_fiberOver_of_isDecent {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDecent Y] (p : FieldValuedPoint Y) :
    List.TFAE
      [ DiscreteTopology (fiberOver f (Points.mk p))
      , topologicalKrullDim (fiberOver f (Points.mk p)) ≤ 0
      , DiscreteTopology (Points (fieldFiber f p))
      , topologicalKrullDim (Points (fieldFiber f p)) ≤ 0
      , dimension (fieldFiber f p) ≤ 0
      , ∀ x : Points X, Points.map f x = Points.mk p → QuasiFiniteAt f x ] :=
  sorry

/-- A locally finite-type morphism between decent algebraic spaces is
quasi-finite at every point of a finite set-theoretic fibre. -/
theorem quasiFiniteAt_fiberOver_of_isDecent_finite {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDecent X]
    [IsDecent Y] (p : FieldValuedPoint Y)
    (hF : (fiberOver f (Points.mk p)).Finite) :
    ∀ x : Points X, Points.map f x = Points.mk p → QuasiFiniteAt f x :=
  sorry

/-- For a locally finite-type morphism between decent algebraic spaces, a
finite set-theoretic fibre gives a finite field-valued fibre over any representative. -/
instance finite_fieldFiber_of_isDecent_finite {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDecent X]
    [IsDecent Y] (p : FieldValuedPoint Y)
    [Finite (fiberOver f (Points.mk p))] :
    Finite (Points (fieldFiber f p)) :=
  sorry

/-- For a locally finite-type morphism, a field-valued fibre has discrete
points if and only if its topological Krull dimension is at most zero. -/
theorem discreteTopology_fieldFiber_iff_topologicalKrullDim_le_zero
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (p : FieldValuedPoint Y) :
    DiscreteTopology (Points (fieldFiber f p)) ↔
      topologicalKrullDim (Points (fieldFiber f p)) ≤ 0 :=
  sorry

/-- For a locally finite-type morphism, a field-valued fibre has topological
Krull dimension at most zero if and only if its étale-local dimension is at most zero. -/
theorem topologicalKrullDim_fieldFiber_le_zero_iff_dimension_le_zero
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (p : FieldValuedPoint Y) :
    topologicalKrullDim (Points (fieldFiber f p)) ≤ 0 ↔
      dimension (fieldFiber f p) ≤ 0 :=
  sorry

/-- A field-valued fibre of a locally finite-type morphism has étale-local
dimension at most zero if and only if the morphism is quasi-finite at every point
over its represented point. -/
theorem dimension_fieldFiber_le_zero_iff_quasiFiniteAt_fiberOver
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (p : FieldValuedPoint Y) :
    dimension (fieldFiber f p) ≤ 0 ↔
      ∀ x : Points X, Points.map f x = Points.mk p → QuasiFiniteAt f x :=
  sorry

/-- Quasi-finiteness at every point mapping to a represented point is
equivalent to quasi-finiteness at every member of its set-theoretic fibre. -/
theorem quasiFiniteAt_fiberOver_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (p : FieldValuedPoint Y) :
    (∀ x : Points X, Points.map f x = Points.mk p → QuasiFiniteAt f x) ↔
      ∀ x ∈ fiberOver f (Points.mk p), QuasiFiniteAt f x :=
  sorry

/-- The structure morphism of a field-valued fibre of a locally finite-type
morphism is locally quasi-finite if and only if the fibre has discrete points. -/
theorem locallyQuasiFinite_fieldFiberToSpec_iff {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (p : FieldValuedPoint Y) :
    LocallyQuasiFinite (fieldFiberToSpec f p) ↔
      DiscreteTopology (Points (fieldFiber f p)) :=
  sorry

/-- The structure morphism of a field-valued fibre of a locally finite-type
morphism is locally quasi-finite if and only if the original morphism is
quasi-finite at every point over its represented point. -/
theorem locallyQuasiFinite_fieldFiberToSpec_iff_quasiFiniteAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (p : FieldValuedPoint Y) :
    LocallyQuasiFinite (fieldFiberToSpec f p) ↔
      ∀ x : Points X, Points.map f x = Points.mk p → QuasiFiniteAt f x :=
  sorry

/-- For a locally finite-type morphism with decent target, the set-theoretic
fibre is discrete if and only if a field-valued fibre over a representative is discrete. -/
theorem discreteTopology_fiberOver_iff_discreteTopology_fieldFiber
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsDecent Y] (p : FieldValuedPoint Y) :
    DiscreteTopology (fiberOver f (Points.mk p)) ↔
      DiscreteTopology (Points (fieldFiber f p)) :=
  sorry

/-- A finite set-theoretic fibre of a locally finite-type morphism between
decent algebraic spaces has discrete topology. -/
instance discreteTopology_fiberOver_of_isDecent_finite {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDecent X]
    [IsDecent Y] (p : FieldValuedPoint Y)
    [Finite (fiberOver f (Points.mk p))] :
    DiscreteTopology (fiberOver f (Points.mk p)) :=
  sorry

/-- For a locally finite-type morphism between decent algebraic spaces, a
finite set-theoretic fibre gives discrete points in every field-valued fibre
over a representative. -/
instance discreteTopology_fieldFiber_of_finite_fiberOver {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDecent X]
    [IsDecent Y] (p : FieldValuedPoint Y)
    [Finite (fiberOver f (Points.mk p))] :
    DiscreteTopology (Points (fieldFiber f p)) :=
  sorry

/-- For a locally finite-type morphism of algebraic spaces and a compatible
point of a field-valued fibre, isolation, closedness with no nontrivial incoming
specialization, vanishing étale-local dimension, and quasi-finiteness at the
image point are equivalent. -/
theorem tfae_fieldFiber_isOpen_dimensionAt_quasiFiniteAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (p : FieldValuedPoint Y) (x : Points X) (xtilde : Points (fieldFiber f p))
    (hxtilde : Points.map (fieldFiberι f p) xtilde = x) :
    List.TFAE
      [ IsOpen ({xtilde} : Set (Points (fieldFiber f p)))
      , (IsClosed ({xtilde} : Set (Points (fieldFiber f p))) ∧
          (∀ xtilde' : Points (fieldFiber f p),
            Specializes xtilde' xtilde → xtilde' = xtilde))
      , dimensionAt xtilde = (0 : WithBot ℕ∞)
      , QuasiFiniteAt f x ] :=
  sorry

/-- For a decent, locally finite-type morphism of algebraic spaces, a point
of a field-valued fibre with local topological Krull dimension zero is isolated. -/
theorem isOpen_fieldFiber_of_topologicalKrullDimAt_eq_zero {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] [Decent f]
    (p : FieldValuedPoint Y) (xtilde : Points (fieldFiber f p))
    (hdim : topologicalKrullDimAt xtilde = (0 : WithBot ℕ∞)) :
    IsOpen ({xtilde} : Set (Points (fieldFiber f p))) :=
  sorry

/-- For a locally finite-type morphism with decent target, isolation and
closedness with no nontrivial incoming specialization in the set-theoretic fibre
are equivalent to the corresponding conditions at any compatible point of a
field-valued fibre, to vanishing étale-local dimension there, and to
quasi-finiteness at the image point. -/
theorem tfae_fiberOver_isOpen_of_isDecent {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDecent Y]
    (p : FieldValuedPoint Y) (x : Points X) (xtilde : Points (fieldFiber f p))
    (hx : Points.map f x = Points.mk p)
    (hxtilde : Points.map (fieldFiberι f p) xtilde = x) :
    List.TFAE
      [ IsOpen ({⟨x, hx⟩} : Set (fiberOver f (Points.mk p)))
      , (IsClosed ({⟨x, hx⟩} : Set (fiberOver f (Points.mk p))) ∧
          (∀ x' : fiberOver f (Points.mk p),
            Specializes x' ⟨x, hx⟩ → x' = ⟨x, hx⟩))
      , IsOpen ({xtilde} : Set (Points (fieldFiber f p)))
      , (IsClosed ({xtilde} : Set (Points (fieldFiber f p))) ∧
          (∀ xtilde' : Points (fieldFiber f p),
            Specializes xtilde' xtilde → xtilde' = xtilde))
      , dimensionAt xtilde = (0 : WithBot ℕ∞)
      , QuasiFiniteAt f x ] :=
  sorry

/-- For a locally finite-type morphism between decent algebraic spaces,
vanishing local topological Krull dimension, isolation, and closedness with no
nontrivial incoming specialization in the set-theoretic fibre and in a
field-valued fibre are equivalent to vanishing étale-local dimension at a
compatible fibre point and to quasi-finiteness at its image. -/
theorem tfae_fiberOver_isOpen_of_isDecent_source_target {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDecent X]
    [IsDecent Y] (p : FieldValuedPoint Y) (x : Points X)
    (xtilde : Points (fieldFiber f p)) (hx : Points.map f x = Points.mk p)
    (hxtilde : Points.map (fieldFiberι f p) xtilde = x) :
    List.TFAE
      [ topologicalKrullDimAt (⟨x, hx⟩ : fiberOver f (Points.mk p)) =
          (0 : WithBot ℕ∞)
      , IsOpen ({⟨x, hx⟩} : Set (fiberOver f (Points.mk p)))
      , (IsClosed ({⟨x, hx⟩} : Set (fiberOver f (Points.mk p))) ∧
          (∀ x' : fiberOver f (Points.mk p),
            Specializes x' ⟨x, hx⟩ → x' = ⟨x, hx⟩))
      , topologicalKrullDimAt xtilde = (0 : WithBot ℕ∞)
      , IsOpen ({xtilde} : Set (Points (fieldFiber f p)))
      , (IsClosed ({xtilde} : Set (Points (fieldFiber f p))) ∧
          (∀ xtilde' : Points (fieldFiber f p),
            Specializes xtilde' xtilde → xtilde' = xtilde))
      , dimensionAt xtilde = (0 : WithBot ℕ∞)
      , QuasiFiniteAt f x ] :=
  sorry

/-- For a locally finite-type morphism of algebraic spaces, a point of a
field-valued fibre is isolated if and only if it is closed and has no nontrivial
incoming specialization. -/
theorem isOpen_singleton_fieldFiber_iff_isClosed_specializes {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (p : FieldValuedPoint Y) (xtilde : Points (fieldFiber f p)) :
    IsOpen ({xtilde} : Set (Points (fieldFiber f p))) ↔
      IsClosed ({xtilde} : Set (Points (fieldFiber f p))) ∧
        ∀ xtilde' : Points (fieldFiber f p),
          Specializes xtilde' xtilde → xtilde' = xtilde :=
  sorry

/-- For a locally finite-type morphism of algebraic spaces, a point of a
field-valued fibre is isolated if and only if the étale-local dimension there
vanishes. -/
theorem isOpen_singleton_fieldFiber_iff_dimensionAt_eq_zero {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (p : FieldValuedPoint Y) (xtilde : Points (fieldFiber f p)) :
    IsOpen ({xtilde} : Set (Points (fieldFiber f p))) ↔
      dimensionAt xtilde = (0 : WithBot ℕ∞) :=
  sorry

/-- For a locally finite-type morphism of algebraic spaces, the étale-local
dimension of a field-valued fibre at a lift of `x` vanishes if and only if `f`
is quasi-finite at `x`. -/
theorem dimensionAt_fieldFiber_eq_zero_iff_quasiFiniteAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (p : FieldValuedPoint Y) (x : Points X) (xtilde : Points (fieldFiber f p))
    (hxtilde : Points.map (fieldFiberι f p) xtilde = x) :
    dimensionAt xtilde = (0 : WithBot ℕ∞) ↔ QuasiFiniteAt f x :=
  sorry

/-- If `Y` is decent, a point of the set-theoretic fibre is isolated if and only
if it is closed in that fibre and has no nontrivial incoming specialization. -/
theorem isOpen_singleton_fiberOver_iff_isClosed_specializes {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDecent Y]
    (p : FieldValuedPoint Y) (x : Points X)
    (hx : Points.map f x = Points.mk p) :
    IsOpen ({⟨x, hx⟩} : Set (fiberOver f (Points.mk p))) ↔
      IsClosed ({⟨x, hx⟩} : Set (fiberOver f (Points.mk p))) ∧
        ∀ x' : fiberOver f (Points.mk p),
          Specializes x' ⟨x, hx⟩ → x' = ⟨x, hx⟩ :=
  sorry

/-- If `Y` is decent, a point of the set-theoretic fibre is isolated if and only
if the corresponding point of the field-valued fibre is isolated. -/
theorem isOpen_singleton_fiberOver_iff_isOpen_singleton_fieldFiber
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsDecent Y] (p : FieldValuedPoint Y)
    (x : Points X) (xtilde : Points (fieldFiber f p))
    (hx : Points.map f x = Points.mk p)
    (hxtilde : Points.map (fieldFiberι f p) xtilde = x) :
    IsOpen ({⟨x, hx⟩} : Set (fiberOver f (Points.mk p))) ↔
      IsOpen ({xtilde} : Set (Points (fieldFiber f p))) :=
  sorry

/-- If `X` and `Y` are decent, vanishing of the local topological Krull dimension
of the set-theoretic fibre at `x` is equivalent to quasi-finiteness of `f` at
`x`. -/
theorem topologicalKrullDimAt_fiberOver_eq_zero_iff_quasiFiniteAt
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsDecent X] [IsDecent Y]
    (p : FieldValuedPoint Y) (x : Points X)
    (hx : Points.map f x = Points.mk p) :
    topologicalKrullDimAt (⟨x, hx⟩ : fiberOver f (Points.mk p)) =
        (0 : WithBot ℕ∞) ↔
      QuasiFiniteAt f x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
