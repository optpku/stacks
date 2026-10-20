/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.MinimalModel

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- The reusable minimal-model predicate and its canonical property API. -/
#check (AlgebraicGeometry.Scheme.Hom.IsMinimalModel :
  {R : Type u} → [CommRing R] → [IsDomain R] → [IsDiscreteValuationRing R] →
    {X : Scheme.{u}} → (X ⟶ Spec (CommRingCat.of R)) → Prop)

/- The flatness instance associated to a minimal-model morphism. -/
#check (AlgebraicGeometry.Scheme.Hom.IsMinimalModel.instFlat :
  ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsMinimalModel f], Flat f)

/- The finite-type instance associated to a minimal-model morphism. -/
#check (AlgebraicGeometry.Scheme.Hom.IsMinimalModel.instFiniteType :
  ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsMinimalModel f], FiniteType f)

/- The properness instance associated to a minimal-model morphism. -/
#check (AlgebraicGeometry.Scheme.Hom.IsMinimalModel.instIsProper :
  ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsMinimalModel f], IsProper f)

/- The defining specification of a minimal-model morphism. -/
#check (AlgebraicGeometry.Scheme.Hom.IsMinimalModel.spec :
  ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsMinimalModel f],
      Flat f ∧ FiniteType f ∧ IsProper f ∧ Scheme.Regular X ∧
        ∀ E : X.IdealSheafData, ¬ IsExceptionalCurveFirstKind E)

end AlgebraicGeometry.Scheme.Hom
