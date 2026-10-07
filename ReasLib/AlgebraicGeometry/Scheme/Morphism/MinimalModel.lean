module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ExceptionalCurve
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Regular

/-!
# Minimal models of curves over discrete valuation rings

This module records the reusable property of a model morphism being proper and regular with no
exceptional curve of the first kind.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism to the spectrum of a discrete valuation ring is a minimal model morphism when it
is flat and of finite type, is proper, has regular source, and its source contains no exceptional
curve of the first kind. -/
class IsMinimalModel {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) : Prop where
  /-- A minimal model is flat over the discrete valuation ring. -/
  flat : Flat f
  /-- A minimal model is of finite type over the discrete valuation ring. -/
  finiteType : FiniteType f
  /-- A minimal model is proper over the discrete valuation ring. -/
  proper : IsProper f
  /-- The source scheme of a minimal model is regular. -/
  regular : Scheme.Regular X
  /-- The source contains no exceptional curve of the first kind. -/
  noExceptionalCurve : ∀ E : X.IdealSheafData, ¬ IsExceptionalCurveFirstKind E

namespace IsMinimalModel

/-- A minimal model morphism is flat. -/
instance instFlat {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsMinimalModel f] : Flat f := sorry

/-- A minimal model morphism is of finite type. -/
instance instFiniteType {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsMinimalModel f] : FiniteType f := sorry

/-- A minimal model morphism is proper. -/
instance instIsProper {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsMinimalModel f] : IsProper f := sorry

/-- The defining properties carried by a minimal model morphism. -/
theorem spec {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsMinimalModel f] :
    Flat f ∧ FiniteType f ∧ IsProper f ∧ Scheme.Regular X ∧
      ∀ E : X.IdealSheafData, ¬ IsExceptionalCurveFirstKind E := sorry

end IsMinimalModel

end AlgebraicGeometry.Scheme.Hom
