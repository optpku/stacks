/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.OrthogonalPointSheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Module
open AlgebraicGeometry.RingedSpace.ModuleDerived
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat
open CategoryTheory.DerivedCategory

noncomputable section

universe u

/- Lemma 57.11.3 (1): vanishing of the shifted morphisms from the residue-field skyscraper
to a perfect complex forces the corresponding cohomology sheaf to vanish on a neighborhood. -/
@[stacks 0G03]
#check (AlgebraicGeometry.Scheme.extSkyscraperToPerfectZeroNear :
    {k : Type u} → [Field k] → (X : SchemeOverField k) →
    [Hom.FiniteType X.hom] → [Regular X.left] →
    (x : X.left) → (hx : x ∈ closedPoints X.left) →
    (K : RingedSpace.ModuleDerived X.left.toRingedSpace) →
    (hK : IsPerfect K) → (i : ℤ) →
    (let kx : ModuleCat (RingCat.of (stalkRing X x)) :=
      ModuleCat.of (RingCat.of (stalkRing X x)) (IsLocalRing.ResidueField (stalkRing X x));
    let Ox := Skyscraper.atPoint x kx;
    let Oxd := (DerivedCategory.singleFunctor X.left.Modules (0 : ℤ)).obj Ox;
    (∀ f : Oxd ⟶ K⟦i⟧, f = 0) →
      ∃ U : X.left.Opens, x ∈ U ∧
        IsZero
          (cohomologySheaf
            ((moduleRestrictionToOpenDerived X.left.toRingedSpace U).obj K)
            (i - (((ringKrullDim (stalkRing X x)).unbotD 0).toNat : ℤ)))))

/- Lemma 57.11.3 (2): vanishing of all shifted morphisms from the residue-field skyscraper
to a perfect complex forces that complex to vanish on a neighborhood. -/
@[stacks 0G03]
#check (AlgebraicGeometry.Scheme.homSkyscraperToPerfectZeroNear :
    {k : Type u} → [Field k] → (X : SchemeOverField k) →
    [Hom.FiniteType X.hom] → [Regular X.left] →
    (x : X.left) → (hx : x ∈ closedPoints X.left) →
    (K : RingedSpace.ModuleDerived X.left.toRingedSpace) →
    (hK : IsPerfect K) →
    (let kx : ModuleCat (RingCat.of (stalkRing X x)) :=
      ModuleCat.of (RingCat.of (stalkRing X x)) (IsLocalRing.ResidueField (stalkRing X x));
    let Ox := Skyscraper.atPoint x kx;
    let Oxd := (DerivedCategory.singleFunctor X.left.Modules (0 : ℤ)).obj Ox;
    (∀ i : ℤ, ∀ f : Oxd ⟶ K⟦i⟧, f = 0) →
      ∃ U : X.left.Opens, x ∈ U ∧
        IsZero ((moduleRestrictionToOpenDerived X.left.toRingedSpace U).obj K)))

/- Lemma 57.11.3 (3): vanishing of the shifted morphisms from a perfect complex to the
residue-field skyscraper forces the cohomology of its dual to vanish on a neighborhood. -/
@[stacks 0G03]
#check (AlgebraicGeometry.Scheme.extPerfectToSkyscraperDualZeroNear :
    {k : Type u} → [Field k] → (X : SchemeOverField k) →
    [Hom.FiniteType X.hom] → [Regular X.left] →
    [KFlat.HomotopyTensorDescends X.left.toRingedSpace] →
    [KFlat.TensorDescends X.left.toRingedSpace] →
    [KFlat.IsLocalization X.left.toRingedSpace] →
    [MonoidalClosed (RingedSpace.ModuleDerived X.left.toRingedSpace)] →
    (x : X.left) → (hx : x ∈ closedPoints X.left) →
    (K : RingedSpace.ModuleDerived X.left.toRingedSpace) →
    (hK : IsPerfect K) → (i : ℤ) →
    (let kx : ModuleCat (RingCat.of (stalkRing X x)) :=
      ModuleCat.of (RingCat.of (stalkRing X x)) (IsLocalRing.ResidueField (stalkRing X x));
    let Ox := Skyscraper.atPoint x kx;
    let Oxd := (DerivedCategory.singleFunctor X.left.Modules (0 : ℤ)).obj Ox;
    (∀ f : K ⟶ Oxd⟦i⟧, f = 0) →
      ∃ U : X.left.Opens, x ∈ U ∧
        IsZero
          (cohomologySheaf
            ((moduleRestrictionToOpenDerived X.left.toRingedSpace U).obj
              (MonoidalClosed.dual K)) i)))

/- Lemma 57.11.3 (4): vanishing of all shifted morphisms from a perfect complex to the
residue-field skyscraper forces that complex to vanish on a neighborhood. -/
@[stacks 0G03]
#check (AlgebraicGeometry.Scheme.homPerfectToSkyscraperZeroNear :
    {k : Type u} → [Field k] → (X : SchemeOverField k) →
    [Hom.FiniteType X.hom] → [Regular X.left] →
    (x : X.left) → (hx : x ∈ closedPoints X.left) →
    (K : RingedSpace.ModuleDerived X.left.toRingedSpace) →
    (hK : IsPerfect K) →
    (let kx : ModuleCat (RingCat.of (stalkRing X x)) :=
      ModuleCat.of (RingCat.of (stalkRing X x)) (IsLocalRing.ResidueField (stalkRing X x));
    let Ox := Skyscraper.atPoint x kx;
    let Oxd := (DerivedCategory.singleFunctor X.left.Modules (0 : ℤ)).obj Ox;
    (∀ i : ℤ, ∀ f : K ⟶ Oxd⟦i⟧, f = 0) →
      ∃ U : X.left.Opens, x ∈ U ∧
        IsZero ((moduleRestrictionToOpenDerived X.left.toRingedSpace U).obj K)))

/- Lemma 57.11.3 (5): vanishing of a derived-tensor cohomology object with the residue-field
skyscraper forces the corresponding cohomology sheaf of the perfect complex to vanish nearby. -/
@[stacks 0G03]
#check (AlgebraicGeometry.Scheme.tensorSkyscraperCohomologyZeroNear :
    {k : Type u} → [Field k] → (X : SchemeOverField k) →
    [Hom.FiniteType X.hom] → [Regular X.left] →
    (x : X.left) → (hx : x ∈ closedPoints X.left) →
    (K : RingedSpace.ModuleDerived X.left.toRingedSpace) →
    (hK : IsPerfect K) → (i : ℤ) →
    (let kx : ModuleCat (RingCat.of (stalkRing X x)) :=
      ModuleCat.of (RingCat.of (stalkRing X x)) (IsLocalRing.ResidueField (stalkRing X x));
    let Ox := Skyscraper.atPoint x kx;
    let Oxd := (DerivedCategory.singleFunctor X.left.Modules (0 : ℤ)).obj Ox;
    IsZero
        ((moduleDerivedCohomologyFunctor X.left.toRingedSpace i).obj
          (DerivedTensor.Right.obj K Oxd)) →
      ∃ U : X.left.Opens, x ∈ U ∧
        IsZero
          (cohomologySheaf
            ((moduleRestrictionToOpenDerived X.left.toRingedSpace U).obj K) i)))

/- Lemma 57.11.3 (6): vanishing of all derived-tensor cohomology objects with the
residue-field skyscraper forces the perfect complex to vanish on a neighborhood. -/
@[stacks 0G03]
#check (AlgebraicGeometry.Scheme.tensorSkyscraperAllZeroNear :
    {k : Type u} → [Field k] → (X : SchemeOverField k) →
    [Hom.FiniteType X.hom] → [Regular X.left] →
    (x : X.left) → (hx : x ∈ closedPoints X.left) →
    (K : RingedSpace.ModuleDerived X.left.toRingedSpace) →
    (hK : IsPerfect K) →
    (let kx : ModuleCat (RingCat.of (stalkRing X x)) :=
      ModuleCat.of (RingCat.of (stalkRing X x)) (IsLocalRing.ResidueField (stalkRing X x));
    let Ox := Skyscraper.atPoint x kx;
    let Oxd := (DerivedCategory.singleFunctor X.left.Modules (0 : ℤ)).obj Ox;
    (∀ i : ℤ,
        IsZero
        ((moduleDerivedCohomologyFunctor X.left.toRingedSpace i).obj
          (DerivedTensor.Right.obj K Oxd))) →
      ∃ U : X.left.Opens, x ∈ U ∧
        IsZero ((moduleRestrictionToOpenDerived X.left.toRingedSpace U).obj K)))
