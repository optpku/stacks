/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Field.Defs
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Skyscraper
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Duality
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.MatlisDuality
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local
public import ReasLib.AlgebraicGeometry.Scheme.Regular
import Mathlib.Tactic.CrossRefAttribute

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

namespace AlgebraicGeometry.Scheme

/-- Vanishing of the shifted morphisms from a residue-field skyscraper to a perfect
derived module forces the corresponding cohomology sheaf to vanish near the point. -/
@[stacks 0G03]
theorem extSkyscraperToPerfectZeroNear
    {k : Type u} [Field k] (X : SchemeOverField k)
    [Hom.FiniteType X.hom] [Regular X.left]
    (x : X.left) (hx : x ∈ closedPoints X.left)
    (K : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (hK : IsPerfect K) (i : ℤ) :
    let kx : ModuleCat (RingCat.of (stalkRing X x)) :=
      ModuleCat.of (RingCat.of (stalkRing X x)) (IsLocalRing.ResidueField (stalkRing X x))
    let Ox := Skyscraper.atPoint x kx
    let Oxd :=
      (DerivedCategory.singleFunctor X.left.Modules (0 : ℤ)).obj Ox
    (∀ f : Oxd ⟶ K⟦i⟧, f = 0) →
      ∃ U : X.left.Opens, x ∈ U ∧
        IsZero
          (cohomologySheaf
            ((moduleRestrictionToOpenDerived X.left.toRingedSpace U).obj K)
            (i - (((ringKrullDim (stalkRing X x)).unbotD 0).toNat : ℤ))) := sorry

/-- Vanishing of all shifted morphisms from a residue-field skyscraper to a perfect
derived module forces that module to vanish near the point. -/
@[stacks 0G03]
theorem homSkyscraperToPerfectZeroNear
    {k : Type u} [Field k] (X : SchemeOverField k)
    [Hom.FiniteType X.hom] [Regular X.left]
    (x : X.left) (hx : x ∈ closedPoints X.left)
    (K : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (hK : IsPerfect K) :
    let kx : ModuleCat (RingCat.of (stalkRing X x)) :=
      ModuleCat.of (RingCat.of (stalkRing X x)) (IsLocalRing.ResidueField (stalkRing X x))
    let Ox := Skyscraper.atPoint x kx
    let Oxd :=
      (DerivedCategory.singleFunctor X.left.Modules (0 : ℤ)).obj Ox
    (∀ i : ℤ, ∀ f : Oxd ⟶ K⟦i⟧, f = 0) →
      ∃ U : X.left.Opens, x ∈ U ∧
        IsZero ((moduleRestrictionToOpenDerived X.left.toRingedSpace U).obj K) := sorry

/-- Vanishing of the shifted morphisms from a perfect derived module to a
residue-field skyscraper forces the cohomology of its dual to vanish near the point. -/
@[stacks 0G03]
theorem extPerfectToSkyscraperDualZeroNear
    {k : Type u} [Field k] (X : SchemeOverField k)
    [Hom.FiniteType X.hom] [Regular X.left]
    [KFlat.HomotopyTensorDescends X.left.toRingedSpace]
    [KFlat.TensorDescends X.left.toRingedSpace]
    [KFlat.IsLocalization X.left.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived X.left.toRingedSpace)]
    (x : X.left) (hx : x ∈ closedPoints X.left)
    (K : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (hK : IsPerfect K) (i : ℤ) :
    let kx : ModuleCat (RingCat.of (stalkRing X x)) :=
      ModuleCat.of (RingCat.of (stalkRing X x)) (IsLocalRing.ResidueField (stalkRing X x))
    let Ox := Skyscraper.atPoint x kx
    let Oxd :=
      (DerivedCategory.singleFunctor X.left.Modules (0 : ℤ)).obj Ox
    (∀ f : K ⟶ Oxd⟦i⟧, f = 0) →
      ∃ U : X.left.Opens, x ∈ U ∧
          IsZero
          (cohomologySheaf
            ((moduleRestrictionToOpenDerived X.left.toRingedSpace U).obj
              (MonoidalClosed.dual K)) i) := sorry

/-- Vanishing of all shifted morphisms from a perfect derived module to a
residue-field skyscraper forces that module to vanish near the point. -/
@[stacks 0G03]
theorem homPerfectToSkyscraperZeroNear
    {k : Type u} [Field k] (X : SchemeOverField k)
    [Hom.FiniteType X.hom] [Regular X.left]
    (x : X.left) (hx : x ∈ closedPoints X.left)
    (K : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (hK : IsPerfect K) :
    let kx : ModuleCat (RingCat.of (stalkRing X x)) :=
      ModuleCat.of (RingCat.of (stalkRing X x)) (IsLocalRing.ResidueField (stalkRing X x))
    let Ox := Skyscraper.atPoint x kx
    let Oxd :=
      (DerivedCategory.singleFunctor X.left.Modules (0 : ℤ)).obj Ox
    (∀ i : ℤ, ∀ f : K ⟶ Oxd⟦i⟧, f = 0) →
      ∃ U : X.left.Opens, x ∈ U ∧
        IsZero ((moduleRestrictionToOpenDerived X.left.toRingedSpace U).obj K) := sorry

/-- Vanishing of a derived-tensor cohomology object with a residue-field skyscraper
forces the corresponding cohomology sheaf of a perfect derived module to vanish nearby. -/
@[stacks 0G03]
theorem tensorSkyscraperCohomologyZeroNear
    {k : Type u} [Field k] (X : SchemeOverField k)
    [Hom.FiniteType X.hom] [Regular X.left]
    (x : X.left) (hx : x ∈ closedPoints X.left)
    (K : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (hK : IsPerfect K) (i : ℤ) :
    let kx : ModuleCat (RingCat.of (stalkRing X x)) :=
      ModuleCat.of (RingCat.of (stalkRing X x)) (IsLocalRing.ResidueField (stalkRing X x))
    let Ox := Skyscraper.atPoint x kx
    let Oxd :=
      (DerivedCategory.singleFunctor X.left.Modules (0 : ℤ)).obj Ox
    IsZero
        ((moduleDerivedCohomologyFunctor X.left.toRingedSpace i).obj
          (DerivedTensor.Right.obj K Oxd)) →
      ∃ U : X.left.Opens, x ∈ U ∧
        IsZero
          (cohomologySheaf
            ((moduleRestrictionToOpenDerived X.left.toRingedSpace U).obj K) i) := sorry

/-- Vanishing of all derived-tensor cohomology objects with a residue-field skyscraper
forces a perfect derived module to vanish near the point. -/
@[stacks 0G03]
theorem tensorSkyscraperAllZeroNear
    {k : Type u} [Field k] (X : SchemeOverField k)
    [Hom.FiniteType X.hom] [Regular X.left]
    (x : X.left) (hx : x ∈ closedPoints X.left)
    (K : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (hK : IsPerfect K) :
    let kx : ModuleCat (RingCat.of (stalkRing X x)) :=
      ModuleCat.of (RingCat.of (stalkRing X x)) (IsLocalRing.ResidueField (stalkRing X x))
    let Ox := Skyscraper.atPoint x kx
    let Oxd :=
      (DerivedCategory.singleFunctor X.left.Modules (0 : ℤ)).obj Ox
    (∀ i : ℤ,
        IsZero
        ((moduleDerivedCohomologyFunctor X.left.toRingedSpace i).obj
          (DerivedTensor.Right.obj K Oxd))) →
      ∃ U : X.left.Opens, x ∈ U ∧
        IsZero ((moduleRestrictionToOpenDerived X.left.toRingedSpace U).obj K) := sorry

end AlgebraicGeometry.Scheme
