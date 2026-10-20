module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.DerivedPushforward
public import ReasLib.CategoryTheory.DerivedCategory.Homology.Conservative
public import ReasLib.AlgebraicGeometry.Scheme.Module.DifferentialOperator.Derived.Coefficients
public import Mathlib.AlgebraicGeometry.Fiber

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSite.Hom RingedSite.Hom.DerivedAdjunction
open AlgebraicGeometry.Scheme.Modules.Kunneth
open scoped MonoidalCategory

-- Local instance justification (defeq pin): ModuleDerived and singleFunctor must use the canonical derived-category presentation of modules on the coefficient ringed site.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.LerayHirsch

/-- The finite biproduct of shifted structure sheaves associated to the degrees `n`. -/
noncomputable abbrev source (Y : Scheme.{u}) {N : ℕ} (n : Fin N → ℕ) :
    RingedSite.Hom.ModuleDerived.{u} (coefficientSite (𝟙 Y)) :=
  ⨁ fun i ↦
    (DerivedCategory.singleFunctor
      (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) (n i : ℤ)).obj
        (𝟙_ (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))))

/-- The source object is the finite biproduct of the degree-`n i` single objects. -/
theorem source_def (Y : Scheme.{u}) {N : ℕ} (n : Fin N → ℕ) :
    source Y n =
      ⨁ fun i ↦
        (DerivedCategory.singleFunctor
          (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) (n i : ℤ)).obj
            (𝟙_ (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y)))) := sorry

/-- The morphism from the finite shifted-unit source classified by the family `ξ`. -/
noncomputable def map {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u}
        (DerivedPushforward.pushforwardHom f))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        ((Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace).map f)))]
    {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, (DerivedCategory.singleFunctor
        (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) (n i : ℤ)).obj
          (𝟙_ (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y)))) ⟶
        (modulePushforwardDerived.{u}
          (DerivedPushforward.pushforwardHom f)).obj
          (DerivedPushforward.derivedComplex f)) :
    source Y n ⟶
      (modulePushforwardDerived.{u}
        (DerivedPushforward.pushforwardHom f)).obj
        (DerivedPushforward.derivedComplex f) :=
  biproduct.desc ξ

/-- The `i`-th biproduct injection followed by `map f n ξ` is `ξ i`. -/
theorem ι_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u}
        (DerivedPushforward.pushforwardHom f))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        ((Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace).map f)))]
    {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, (DerivedCategory.singleFunctor
        (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) (n i : ℤ)).obj
          (𝟙_ (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y)))) ⟶
        (modulePushforwardDerived.{u}
          (DerivedPushforward.pushforwardHom f)).obj
          (DerivedPushforward.derivedComplex f))
    (i : Fin N) :
    biproduct.ι (fun j ↦
        (DerivedCategory.singleFunctor
          (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) (n j : ℤ)).obj
            (𝟙_ (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))))) i ≫
      map f n ξ = ξ i := sorry

/-- The restriction of `map f n ξ` to the residue-field fiber at `y`, followed by the
canonical comparison with the derived de Rham pushforward of that fiber. -/
noncomputable def fiberMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u}
        (DerivedPushforward.pushforwardHom f))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        ((Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace).map f)))]
    [DerivedAdjunction.HasPair.{u} (DerivedPushforward.pushforwardHom f)]
    {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, (DerivedCategory.singleFunctor
        (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) (n i : ℤ)).obj
          (𝟙_ (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y)))) ⟶
        (modulePushforwardDerived.{u}
          (DerivedPushforward.pushforwardHom f)).obj
          (DerivedPushforward.derivedComplex f))
    (y : Y)
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u}
        (DerivedPushforward.pushforwardHom (f.fiberToSpecResidueField y)))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        ((Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace).map
            (f.fiberToSpecResidueField y))))]
    [DerivedAdjunction.HasPair.{u}
      (DerivedPushforward.pushforwardHom (f.fiberToSpecResidueField y))] :=
  (modulePullbackDerived.{u}
      (DerivedPushforward.basePullbackHom (Y.fromSpecResidueField y))).map
      (map f n ξ) ≫
    DerivedPushforward.pushforwardDerivedComplexBaseChangeMap
      (f.fiberι y) (f.fiberToSpecResidueField y) f (Y.fromSpecResidueField y)
      (IsPullback.of_hasPullback f (Y.fromSpecResidueField y))

/-- The fiber map is derived pullback followed by the canonical de Rham base-change map. -/
theorem fiberMap_def {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u}
        (DerivedPushforward.pushforwardHom f))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        ((Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace).map f)))]
    [DerivedAdjunction.HasPair.{u} (DerivedPushforward.pushforwardHom f)]
    {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, (DerivedCategory.singleFunctor
        (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) (n i : ℤ)).obj
          (𝟙_ (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y)))) ⟶
        (modulePushforwardDerived.{u}
          (DerivedPushforward.pushforwardHom f)).obj
          (DerivedPushforward.derivedComplex f))
    (y : Y)
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u}
        (DerivedPushforward.pushforwardHom (f.fiberToSpecResidueField y)))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        ((Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace).map
            (f.fiberToSpecResidueField y))))]
    [DerivedAdjunction.HasPair.{u}
      (DerivedPushforward.pushforwardHom (f.fiberToSpecResidueField y))] :
    fiberMap f n ξ y =
      (modulePullbackDerived.{u}
          (DerivedPushforward.basePullbackHom (Y.fromSpecResidueField y))).map
          (map f n ξ) ≫
        DerivedPushforward.pushforwardDerivedComplexBaseChangeMap
          (f.fiberι y) (f.fiberToSpecResidueField y) f (Y.fromSpecResidueField y)
          (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)) := sorry

/-- The classes `ξ` form a basis on every residue-field fiber when their canonical fiber
maps are isomorphisms. -/
def IsFiberwiseBasis {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u}
        (DerivedPushforward.pushforwardHom f))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        ((Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace).map f)))]
    [DerivedAdjunction.HasPair.{u} (DerivedPushforward.pushforwardHom f)]
    {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, (DerivedCategory.singleFunctor
        (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) (n i : ℤ)).obj
          (𝟙_ (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y)))) ⟶
        (modulePushforwardDerived.{u}
          (DerivedPushforward.pushforwardHom f)).obj
          (DerivedPushforward.derivedComplex f))
    [∀ y : Y, Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u}
        (DerivedPushforward.pushforwardHom (f.fiberToSpecResidueField y)))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        ((Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace).map
            (f.fiberToSpecResidueField y))))]
    [∀ y : Y, DerivedAdjunction.HasPair.{u}
      (DerivedPushforward.pushforwardHom (f.fiberToSpecResidueField y))] : Prop :=
  ∀ y : Y, IsIso (fiberMap f n ξ y)

/-- Fiberwise basis means pointwise invertibility of the canonical residue-field fiber map. -/
theorem isFiberwiseBasis_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u}
        (DerivedPushforward.pushforwardHom f))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        ((Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace).map f)))]
    [DerivedAdjunction.HasPair.{u} (DerivedPushforward.pushforwardHom f)]
    {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, (DerivedCategory.singleFunctor
        (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) (n i : ℤ)).obj
          (𝟙_ (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y)))) ⟶
        (modulePushforwardDerived.{u}
          (DerivedPushforward.pushforwardHom f)).obj
          (DerivedPushforward.derivedComplex f))
    [∀ y : Y, Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u}
        (DerivedPushforward.pushforwardHom (f.fiberToSpecResidueField y)))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        ((Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace).map
            (f.fiberToSpecResidueField y))))]
    [∀ y : Y, DerivedAdjunction.HasPair.{u}
      (DerivedPushforward.pushforwardHom (f.fiberToSpecResidueField y))] :
    IsFiberwiseBasis f n ξ ↔ ∀ y : Y, IsIso (fiberMap f n ξ y) := sorry

/-- Fiberwise basis is equivalently detected on every homology map of every residue-field
fiber map. -/
theorem isFiberwiseBasis_iff_homology {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u}
        (DerivedPushforward.pushforwardHom f))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        ((Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace).map f)))]
    [DerivedAdjunction.HasPair.{u} (DerivedPushforward.pushforwardHom f)]
    {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, (DerivedCategory.singleFunctor
        (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) (n i : ℤ)).obj
          (𝟙_ (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y)))) ⟶
        (modulePushforwardDerived.{u}
          (DerivedPushforward.pushforwardHom f)).obj
          (DerivedPushforward.derivedComplex f))
    [∀ y : Y, Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u}
        (DerivedPushforward.pushforwardHom (f.fiberToSpecResidueField y)))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        ((Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace).map
            (f.fiberToSpecResidueField y))))]
    [∀ y : Y, DerivedAdjunction.HasPair.{u}
      (DerivedPushforward.pushforwardHom (f.fiberToSpecResidueField y))] :
    IsFiberwiseBasis f n ξ ↔
      ∀ (y : Y) (q : ℤ),
        IsIso ((DerivedCategory.homologyFunctor
          (RingedSite.ModuleCat.{u, u, u, u}
            (coefficientSite (𝟙 (Spec (Y.residueField y))))) q).map
              (fiberMap f n ξ y)) := sorry

/-- Smooth properness and a fibrewise basis imply that the Leray--Hirsch map is an isomorphism. -/
theorem map_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [IsProper f]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u}
        (DerivedPushforward.pushforwardHom f))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        ((Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace).map f)))]
    [DerivedAdjunction.HasPair.{u} (DerivedPushforward.pushforwardHom f)]
    {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, (DerivedCategory.singleFunctor
        (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) (n i : ℤ)).obj
          (𝟙_ (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y)))) ⟶
        (modulePushforwardDerived.{u}
          (DerivedPushforward.pushforwardHom f)).obj
          (DerivedPushforward.derivedComplex f))
    [∀ y : Y, Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u}
        (DerivedPushforward.pushforwardHom (f.fiberToSpecResidueField y)))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        ((Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace).map
            (f.fiberToSpecResidueField y))))]
    [∀ y : Y, DerivedAdjunction.HasPair.{u}
      (DerivedPushforward.pushforwardHom (f.fiberToSpecResidueField y))]
    (hξ : IsFiberwiseBasis f n ξ) :
    IsIso (map f n ξ) := sorry

end AlgebraicGeometry.Scheme.DeRham.LerayHirsch
