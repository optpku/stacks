/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Determinant
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Core

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PerfectDerived

/-- Perfect derived `ᵊa_X`-modules have quasi-coherent homology. -/
theorem isDerivedQuasiCoherent (X : Scheme.{u})
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :
    DerivedCategory.cohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) K.obj := sorry

/-- The canonical functor from perfect derived `ᵊa_X`-modules to derived modules with
quasi-coherent homology. -/
def toDerivedQCoh (X : Scheme.{u}) :
    RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace) ⥤
      DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) :=
  (DerivedCategory.cohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).lift
    (RingedSpace.ModuleDerived.Perfect.ι (X := X.toRingedSpace))
    (fun K ↦ isDerivedQuasiCoherent X K)

/-- Forgetting the quasi-coherent lift leaves the underlying perfect derived object unchanged. -/
theorem toDerivedQCoh_obj (X : Scheme.{u})
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :
    ((DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι.obj
      ((toDerivedQCoh X).obj K)) = K.obj := sorry

/-- Perfect derived `ᵊa_X`-modules with Tor-amplitude contained in `[-1, 0]`. -/
abbrev TorNegOneZero (X : Scheme.{u})
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)] : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    (fun K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace) ↦
      RingedSpace.HasTorAmplitudeIn K.obj (-1) 0)

namespace TorNegOneZero

/-- The inclusion of perfect derived objects with Tor-amplitude in `[-1, 0]`. -/
def ι (X : Scheme.{u})
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)] :
    TorNegOneZero X ⥤ RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace) :=
  ObjectProperty.ι _

/-- An object of `TorNegOneZero X` is perfect. -/
theorem isPerfect (X : Scheme.{u})
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)] (K : TorNegOneZero X) :
    RingedSpace.ModuleDerived.IsPerfect K.obj.obj := sorry

/-- An object of `TorNegOneZero X` has Tor-amplitude contained in `[-1, 0]`. -/
theorem hasTorAmplitudeIn (X : Scheme.{u})
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)] (K : TorNegOneZero X) :
    RingedSpace.HasTorAmplitudeIn K.obj.obj (-1) 0 := sorry

/-- Derived sections of a perfect object over an affine open, before recording perfectness and
Tor-amplitude of the result. -/
def affineDerivedSections (X : Scheme.{u})
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)] (U : X.affineOpens) :
    TorNegOneZero X ⥤ DerivedCategory (ModuleCat Γ(X, U.1)) :=
  ι X ⋙ toDerivedQCoh X ⋙ DerivedQCoh.pullback U.1.ι ⋙
    DerivedQCoh.pullback U.2.isoSpec.inv ⋙ DerivedQCoh.affineGlobalSections Γ(X, U.1)

/-- Affine derived sections are given by restriction to the open, transport to its spectrum,
and derived global sections. -/
theorem affineDerivedSections_obj (X : Scheme.{u})
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)] (U : X.affineOpens)
    (K : TorNegOneZero X) :
    (affineDerivedSections X U).obj K =
      (DerivedQCoh.affineGlobalSections Γ(X, U.1)).obj
        ((DerivedQCoh.pullback U.2.isoSpec.inv).obj
          ((DerivedQCoh.pullback U.1.ι).obj ((toDerivedQCoh X).obj K.obj))) := sorry

/-- Affine derived sections of a perfect object are perfect. -/
theorem affineDerivedSections_isPerfect (X : Scheme.{u})
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)] (U : X.affineOpens)
    (K : TorNegOneZero X) :
    DerivedCategory.IsPerfect ((affineDerivedSections X U).obj K) := sorry

/-- Affine derived sections, lifted to perfect derived modules. -/
def affinePerfectSections (X : Scheme.{u})
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)] (U : X.affineOpens) :
    TorNegOneZero X ⥤ CategoryTheory.PerfectDerived Γ(X, U.1) :=
  ObjectProperty.lift
    (DerivedCategory.IsPerfect :
      ObjectProperty (DerivedCategory (ModuleCat Γ(X, U.1))))
    (affineDerivedSections X U) (affineDerivedSections_isPerfect X U)

/-- Forgetting affine perfectness recovers affine derived sections. -/
theorem affinePerfectSections_obj (X : Scheme.{u})
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)] (U : X.affineOpens)
    (K : TorNegOneZero X) :
    ((affinePerfectSections X U).obj K).obj = (affineDerivedSections X U).obj K := sorry

/-- Affine derived sections preserve Tor-amplitude in `[-1, 0]`. -/
theorem affinePerfectSections_hasTorAmplitudeIn (X : Scheme.{u})
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    (U : X.affineOpens) (K : TorNegOneZero X) :
    DerivedCategory.HasTorAmplitudeIn (R := Γ(X, U.1))
      ((affinePerfectSections X U).obj K).obj (-1) 0 := sorry

/-- The affine-sections functor from scheme-perfect objects of Tor-amplitude `[-1, 0]` to the
corresponding ring-theoretic determinant domain. -/
def affineSections (X : Scheme.{u})
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)] (U : X.affineOpens) :
    TorNegOneZero X ⥤ CategoryTheory.PerfectDerived.TorNegOneZero Γ(X, U.1) :=
  ObjectProperty.lift ((fun K : CategoryTheory.PerfectDerived Γ(X, U.1) ↦
      DerivedCategory.HasTorAmplitudeIn (R := Γ(X, U.1)) K.obj (-1) 0) :
      ObjectProperty (CategoryTheory.PerfectDerived Γ(X, U.1)))
    (affinePerfectSections X U) (affinePerfectSections_hasTorAmplitudeIn X U)

/-- Forgetting the two affine full-subcategory conditions recovers affine derived sections. -/
theorem affineSections_obj (X : Scheme.{u})
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)] (U : X.affineOpens)
    (K : TorNegOneZero X) :
    ((affineSections X U).obj K).obj.obj = (affineDerivedSections X U).obj K := sorry

/-- The functor of affine sections of the global determinant line. -/
def lineSectionsFunctor (X : Scheme.{u})
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    (F : CategoryTheory.Core (TorNegOneZero X) ⥤ Scheme.Modules.Invertible.Core X)
    (U : X.affineOpens) :
    CategoryTheory.Core (TorNegOneZero X) ⥤ ModuleCat Γ(X, U.1) :=
  F ⋙ Scheme.Modules.Invertible.sections X U.1

/-- The affine-sections line functor evaluates the underlying global determinant line. -/
theorem lineSectionsFunctor_obj (X : Scheme.{u})
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    (F : CategoryTheory.Core (TorNegOneZero X) ⥤ Scheme.Modules.Invertible.Core X)
    (U : X.affineOpens) (K : CategoryTheory.Core (TorNegOneZero X)) :
    (lineSectionsFunctor X F U).obj K =
      (Scheme.Modules.Invertible.sections X U.1).obj (F.obj K) := sorry

/-- The line-valued functor underlying an affine ring-level determinant construction. -/
def affineLineFunctor (X : Scheme.{u}) (U : X.affineOpens)
    (D : CategoryTheory.PerfectDerived.TorNegOneZero.Determinant Γ(X, U.1)) :
    CategoryTheory.Core (CategoryTheory.PerfectDerived.TorNegOneZero Γ(X, U.1)) ⥤
      ModuleCat Γ(X, U.1) :=
  D.det ⋙ CategoryTheory.Core.inclusion _ ⋙ ObjectProperty.ι _

/-- The affine line functor forgets the invertibility witness from the ring-level determinant. -/
theorem affineLineFunctor_obj (X : Scheme.{u}) (U : X.affineOpens)
    (D : CategoryTheory.PerfectDerived.TorNegOneZero.Determinant Γ(X, U.1))
    (K : CategoryTheory.Core (CategoryTheory.PerfectDerived.TorNegOneZero Γ(X, U.1))) :
    (affineLineFunctor X U D).obj K = (D.det.obj K).of.obj := sorry

/-- A coherent determinant construction for perfect derived modules on a scheme with
Tor-amplitude in `[-1, 0]`. -/
structure Determinant (X : Scheme.{u})
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)] where
  /-- The determinant functor from the core of perfect objects to invertible modules. -/
  det : CategoryTheory.Core (TorNegOneZero X) ⥤ Scheme.Modules.Invertible.Core X
  /-- The isomorphism-invariant rank-zero predicate. -/
  isRankZero : TorNegOneZero X → Prop
  /-- Rank zero is invariant under derived isomorphism. -/
  rankZero_iff_iso :
    ∀ {K L : TorNegOneZero X}, CategoryTheory.Iso K L →
      (isRankZero K ↔ isRankZero L)
  /-- The canonical global section of the determinant line of a rank-zero object. -/
  canonicalElement :
    ∀ (K : TorNegOneZero X), isRankZero K → Γ((det.obj ⟨K⟩).of.obj, ⊤)
  /-- The determinant functor carries canonical sections through isomorphisms. -/
  map_canonicalElement :
    ∀ {K L : TorNegOneZero X} (a : K ≅ L) (hK : isRankZero K),
      RingedSpace.Modules.Hom.app (det.map ⟨a⟩).iso.hom.hom ⊤
          (canonicalElement K hK) =
        canonicalElement L ((rankZero_iff_iso a).mp hK)
  /-- A coherent ring-level determinant construction on every affine open. -/
  affineDeterminant :
    ∀ U : X.affineOpens,
      CategoryTheory.PerfectDerived.TorNegOneZero.Determinant Γ(X, U.1)
  /-- Affine sections of global determinant lines agree naturally with ring-level determinant
  lines. -/
  affineComparison :
    ∀ U : X.affineOpens,
      lineSectionsFunctor X det U ≅
        (affineSections X U).core ⋙ affineLineFunctor X U (affineDeterminant U)
  /-- Rank zero is exactly the affine-local rank-zero condition. -/
  affine_rankZero :
    ∀ K : TorNegOneZero X,
      isRankZero K ↔
        ∀ U : X.affineOpens,
          (affineDeterminant U).isRankZero ((affineSections X U).obj K)
  /-- The affine comparison carries the restriction of the global canonical section to the
  ring-level canonical element. -/
  affine_canonicalElement :
    ∀ (K : TorNegOneZero X) (hK : isRankZero K) (U : X.affineOpens),
      ((affineComparison U).hom.app ⟨K⟩).hom
          (((det.obj ⟨K⟩).of.obj.presheaf.map (homOfLE le_top).op).hom
            (canonicalElement K hK)) =
        (affineDeterminant U).canonicalElement ((affineSections X U).obj K)
          ((affine_rankZero K).mp hK U)

namespace Determinant

variable {X : Scheme.{u}}
variable [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]

/-- The invertible module underlying the determinant of a perfect derived object. -/
def line (D : Determinant X) (K : TorNegOneZero X) : X.Modules :=
  (D.det.obj ⟨K⟩).of.obj

/-- The determinant line is the module underlying the value of the determinant functor. -/
theorem line_def (D : Determinant X) (K : TorNegOneZero X) :
    D.line K = (D.det.obj ⟨K⟩).of.obj := sorry

/-- Rank zero is detected by every affine restriction and its chosen ring-level determinant. -/
theorem rankZero_iff_affine (D : Determinant X)
    (K : TorNegOneZero X) :
    D.isRankZero K ↔
      ∀ U : X.affineOpens,
        (D.affineDeterminant U).isRankZero ((affineSections X U).obj K) := sorry

/-- On an affine open, the determinant comparison sends the restricted canonical section to
the ring-level canonical element. -/
theorem canonicalElement_affine (D : Determinant X)
    (K : TorNegOneZero X) (hK : D.isRankZero K) (U : X.affineOpens) :
    ((D.affineComparison U).hom.app ⟨K⟩).hom
        (((D.line K).presheaf.map (homOfLE le_top).op).hom
          (D.canonicalElement K hK)) =
      (D.affineDeterminant U).canonicalElement ((affineSections X U).obj K)
        ((D.rankZero_iff_affine K).mp hK U) := sorry

end Determinant

/-- Every scheme admits a coherent determinant construction on perfect derived modules of
Tor-amplitude in `[-1, 0]`, compatible with affine restriction. -/
theorem nonemptyDeterminant (X : Scheme.{u})
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)] : Nonempty (Determinant X) := sorry

end TorNegOneZero

end AlgebraicGeometry.Scheme.PerfectDerived

end
