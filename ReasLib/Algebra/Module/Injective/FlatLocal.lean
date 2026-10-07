module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Injective
public import ReasLib.Algebra.Module.Injective.Hull
public import ReasLib.Algebra.Module.Injective.MaximalIdeal
public import ReasLib.LinearAlgebra.TensorProduct.RightModule
public import ReasLib.RingTheory.RingHom.Local.MaximalIdeal

@[expose] public section

open IsLocalRing
open scoped TensorProduct TensorProduct.Right

universe u v w

namespace LinearMap.IsInjectiveHull

/-- A flat local homomorphism identifying the residue fields identifies chosen injective
hulls of those residue fields after restriction of scalars. -/
theorem nonempty_iso_restrictScalars_of_flat_local
    {R : Type u} {S : Type v} {ER ES : Type w}
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    [AddCommGroup ER] [Module R ER] [Module.Injective R ER]
    [AddCommGroup ES] [Module S ES] [Module.Injective S ES]
    (f : R →+* S) [IsLocalHom f] (hflat : f.Flat)
    (hres : Function.Bijective
      (Ideal.quotientMap ((IsLocalRing.maximalIdeal R).map f) f Ideal.le_comap_map))
    (iotaR : IsLocalRing.ResidueField R →ₗ[R] ER) (hiotaR : iotaR.IsInjectiveHull)
    (iotaS : IsLocalRing.ResidueField S →ₗ[S] ES) (hiotaS : iotaS.IsInjectiveHull) :
    Nonempty
      (ModuleCat.of R ER ≅
        (ModuleCat.restrictScalars f).obj (ModuleCat.of S ES)) := sorry

/-- The maximal ideal of `B` annihilates the tensor of a residue-field generator with
`1 : B` when the maximal ideal of `B` is extended from `A`. -/
theorem maximalIdeal_le_ker_baseChangeGenerator
    {A : Type u} {B : Type v} {E : Type w}
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
    [AddCommGroup E] [Module A E]
    (hmax : (algebraMap A B).MapsMaximalIdeal)
    (iota : ResidueField A →ₗ[A] E) :
    maximalIdeal B ≤ LinearMap.ker
      (LinearMap.toSpanSingleton B (E ⊗[A] B) (iota 1 ⊗ₜ[A] (1 : B))) := sorry

/-- The quotient-lifted residue-field map into the scalar extension of a module. -/
noncomputable def baseChangeResidueMap
    {A : Type u} {B : Type v} {E : Type w}
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
    [AddCommGroup E] [Module A E]
    (hmax : (algebraMap A B).MapsMaximalIdeal)
    (iota : ResidueField A →ₗ[A] E) :
    ResidueField B →ₗ[B] E ⊗[A] B :=
  (maximalIdeal B).liftQ
    (LinearMap.toSpanSingleton B (E ⊗[A] B) (iota 1 ⊗ₜ[A] (1 : B)))
    (maximalIdeal_le_ker_baseChangeGenerator hmax iota)

/-- The base-changed residue-field map sends the residue of `b : B` to
`b • (iota 1 ⊗ₜ[A] 1)`. -/
@[simp]
theorem baseChangeResidueMap_residue
    {A : Type u} {B : Type v} {E : Type w}
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
    [AddCommGroup E] [Module A E]
    (hmax : (algebraMap A B).MapsMaximalIdeal)
    (iota : ResidueField A →ₗ[A] E) (b : B) :
    baseChangeResidueMap hmax iota (residue B b) =
      b • (iota 1 ⊗ₜ[A] (1 : B)) := sorry

/-- Flat local base change along a map extending the maximal ideal preserves injectivity of an
injective hull of the residue field. -/
theorem injective_tensorProduct_of_flat_of_mapsMaximalIdeal
    {A : Type u} {B : Type v} {E : Type w}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    [AddCommGroup E] [Module A E] [Module.Injective A E]
    (hmax : (algebraMap A B).MapsMaximalIdeal)
    (iota : ResidueField A →ₗ[A] E) (hiota : iota.IsInjectiveHull) :
    Module.Injective B (E ⊗[A] B) := sorry

/-- For a flat local map of Noetherian local rings extending the maximal ideal, scalar extension
of an injective hull of the source residue field is an injective hull of the target residue field. -/
theorem baseChange_of_flat_of_mapsMaximalIdeal
    {A : Type u} {B : Type v} {E : Type w}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    [AddCommGroup E] [Module A E] [Module.Injective A E]
    (hmax : (algebraMap A B).MapsMaximalIdeal)
    (iota : ResidueField A →ₗ[A] E) (hiota : iota.IsInjectiveHull) :
    @LinearMap.IsInjectiveHull B _ (ResidueField B) _ _ (E ⊗[A] B) _ _
      (injective_tensorProduct_of_flat_of_mapsMaximalIdeal hmax iota hiota)
      (baseChangeResidueMap hmax iota) := sorry

end LinearMap.IsInjectiveHull
