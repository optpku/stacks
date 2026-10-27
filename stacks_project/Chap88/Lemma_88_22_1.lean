/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.FlatLocus
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.FlatLocus.Affine

/-!
# Lemma 88.22.1

A locally Noetherian formal algebraic space over a complete discrete valuation
ring admits a closed flat formal subspace with universal factorization from
locally Noetherian formal spaces flat over the base.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Lemma 88.22.1: The flat locus is a closed flat formal subspace through which
every morphism from a locally Noetherian formal space flat over the base factors. -/
@[stacks 0GD8] #check (AlgebraicGeometry.FormalAlgebraicSpace.flatLocus_spec :
  ∀ {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    (hA : Spec (.of A) ⟶ S) {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] (p : X ⟶ spf A hA),
    ClosedImmersion (flatLocusι p) ∧ Flat (flatLocusι p ≫ p) ∧
      (∀ {Y : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace Y]
        [IsLocallyNoetherian Y] (g : Y ⟶ X) [Flat (g ≫ p)],
        lift p g ≫ flatLocusι p = g))

#check (AlgebraicGeometry.FormalAlgebraicSpace.instClosedImmersion_flatLocusι :
  ∀ {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    (hA : Spec (.of A) ⟶ S) {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] (p : X ⟶ spf A hA),
    ClosedImmersion (flatLocusι p))

#check (AlgebraicGeometry.FormalAlgebraicSpace.instFlat_flatLocusToSpf :
  ∀ {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    (hA : Spec (.of A) ⟶ S) {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] (p : X ⟶ spf A hA),
    Flat (flatLocusι p ≫ p))

#check (AlgebraicGeometry.FormalAlgebraicSpace.factorsThrough_flatLocus :
  ∀ {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    (hA : Spec (.of A) ⟶ S) {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] (p : X ⟶ spf A hA)
    {Y : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian Y] (g : Y ⟶ X) [Flat (g ≫ p)],
    lift p g ≫ flatLocusι p = g)
