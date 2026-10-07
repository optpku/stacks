module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Cech.Universal
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Injective
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.DeltaFunctor.Connecting
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Properties
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Universality
public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Universal.Iso
import Mathlib.Tactic.CrossRefAttribute

/-!
# Right-derived Cech cohomology

The degree-zero Cech cohomology functor has a canonical bounded-below right-derived model. The
comparison is owned at the delta-functor level: its degree-zero component is the canonical
right-derived comparison, and universality extends it to every degree.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.CohomologicalDeltaFunctor
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe u v w d

namespace SheafOfModules.RingedSite.Cech

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J RingCat.{w}) (U : C) [HasFiniteProducts (Over U)]
variable {ι : Type w} (family : ι → Over U)
variable [EnoughInjectives (PresheafOfModules.{w} 𝒪.obj)]

section Derived

variable [HasDerivedCategory.{d} (PresheafOfModules.{w} 𝒪.obj)]
variable [HasDerivedCategory.{d} (ModuleCat.{w} (𝒪.obj.obj (op U)))]

/-- The underived degree-zero Cech cohomology functor. -/
@[stacks 01EN "underived degree-zero Cech cohomology"]
abbrev degreeZero : PresheafOfModules.{w} 𝒪.obj ⥤
    ModuleCat.{w} (𝒪.obj.obj (op U)) :=
  (degree 𝒪 U family 0).obj

/-- The canonical bounded-below right-derived functor of degree-zero Cech cohomology. -/
@[stacks 015A "bounded right-derived degree-zero Cech cohomology"]
abbrev rightDerived :
    DerivedCategory.Plus (PresheafOfModules.{w} 𝒪.obj) ⥤
      DerivedCategory.Plus (ModuleCat.{w} (𝒪.obj.obj (op U))) :=
  Functor.RightDerived.Bounded.functor (degreeZero 𝒪 U family)

/-- The cohomological delta functor formed from the canonical right-derived Cech functor. -/
@[stacks 05TE "right-derived Cech delta functor"]
abbrev derivedDeltaFunctor :
    CohomologicalDeltaFunctor (PresheafOfModules.{w} 𝒪.obj)
      (ModuleCat.{w} (𝒪.obj.obj (op U))) :=
  Functor.RightDerived.cohomological (rightDerived 𝒪 U family)

/-- The canonical degree-zero comparison from Cech cohomology to its bounded right-derived
degree-zero functor. -/
noncomputable def zeroIso
    (hF : PreservesFiniteLimits (degreeZero 𝒪 U family)) :
    ((deltaFunctor 𝒪 U family 0).obj) ≅ ((derivedDeltaFunctor 𝒪 U family 0).obj) :=
  @asIso _ _ _ _ (Functor.RightDerived.Bounded.zero (degreeZero 𝒪 U family))
    ((Functor.RightDerived.Bounded.zero.isIso_iff_preservesFiniteLimits
      (degreeZero 𝒪 U family)).2 hF) ≪≫
    (Functor.RightDerived.cohomological.degreeIso
      (rightDerived 𝒪 U family) 0).symm

/-- The zero-degree comparison with the canonical left-exactness certificate supplied by the
abstract Cech delta-functor interface. -/
@[stacks 01EN "canonical zero-degree Cech comparison"]
noncomputable def canonicalZeroIso :
    ((deltaFunctor 𝒪 U family 0).obj) ≅ ((derivedDeltaFunctor 𝒪 U family 0).obj) :=
  zeroIso 𝒪 U family
    (CohomologicalDeltaFunctor.degreeZeroPreservesFiniteLimits
      (deltaFunctor 𝒪 U family))

/-- The canonical comparison of the Cech and right-derived cohomological delta functors. -/
@[stacks 01EN "Cech and right-derived delta-functor comparison"]
noncomputable def deltaIso
    (hCech : IsUniversal (deltaFunctor 𝒪 U family))
    (hDerived : IsUniversal (derivedDeltaFunctor 𝒪 U family)) :
    deltaFunctor 𝒪 U family ≅ derivedDeltaFunctor 𝒪 U family :=
  IsUniversal.isoOf hCech hDerived (canonicalZeroIso 𝒪 U family)

/-- The canonical comparison using the universal presheaf-module Cech instance and a supplied
right-derived universality proof. -/
@[stacks 01EN "canonical universal Cech comparison"]
noncomputable def canonicalDeltaIso :
    deltaFunctor 𝒪 U family ≅ derivedDeltaFunctor 𝒪 U family :=
  deltaIso 𝒪 U family (deltaFunctor.isUniversal 𝒪 U family)
    (Functor.RightDerived.Bounded.cohomological.isUniversal
      (degreeZero 𝒪 U family))

/-- The degree-`n` comparison between Cech cohomology and the corresponding right-derived degree.
-/
@[stacks 01EN "degreewise Cech and right-derived comparison"]
noncomputable def degreeIso
    (hCech : IsUniversal (deltaFunctor 𝒪 U family))
    (hDerived : IsUniversal (derivedDeltaFunctor 𝒪 U family)) (n : ℕ) :
    (degree 𝒪 U family n).obj ≅
      Functor.RightDerived.Bounded.degree (degreeZero 𝒪 U family) (n : ℤ) :=
  CohomologicalDeltaFunctor.Iso.app (deltaIso 𝒪 U family hCech hDerived) n ≪≫
    (Functor.RightDerived.cohomological.degreeIso
      (rightDerived 𝒪 U family) n)

/-- The degreewise comparison using the canonical Cech universal instance. -/
@[stacks 01EN "canonical degreewise Cech comparison"]
noncomputable def canonicalDegreeIso (n : ℕ) :
    (degree 𝒪 U family n).obj ≅
      Functor.RightDerived.Bounded.degree (degreeZero 𝒪 U family) (n : ℤ) :=
  degreeIso 𝒪 U family (deltaFunctor.isUniversal 𝒪 U family)
    (Functor.RightDerived.Bounded.cohomological.isUniversal
      (degreeZero 𝒪 U family)) n

end Derived

end SheafOfModules.RingedSite.Cech
