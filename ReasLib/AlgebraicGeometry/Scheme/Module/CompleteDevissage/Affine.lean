/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.CompleteDevissageAtAmbientPoint
public import ReasLib.Algebra.Module.Devissage.CompleteAt
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Affine

/-!
# Complete dévissages of affine module sheaves

This module compares geometric complete dévissages of an affine module sheaf with
complete dévissages of the corresponding module.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace ModuleCat

/-- For a finite-type ring map and a finite module, existence of a complete dévissage of
the associated affine module sheaf over a point implies existence of a complete algebraic
dévissage over that point. -/
theorem exists_completeDevissageOver_of_tilde
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (hf : f.FiniteType)
    (N : ModuleCat.{u} B) [Module.Finite B N]
    (p : PrimeSpectrum A) (q : PrimeSpectrum B) (hq : PrimeSpectrum.comap f q = p) :
    let S : FGAlgCat.{u} A := ⟨@CommAlgCat.of A _ B _ f.toAlgebra, hf⟩
    let M : FGModuleCat.{u} S.obj := ⟨N, (ModuleCat.isFG_iff N).2 inferInstance⟩
    let hMap : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom f)) :=
      HasRingHomProperty.Spec_iff.mpr hf
    let hTilde :=
      (@Scheme.Modules.tilde_isFiniteType_iff_module_finite (CommRingCat.of B) N).mpr
        (inferInstance : Module.Finite B N)
    Nonempty (@CompleteDevissageOver
      (Spec (.of A)) (Spec (.of B)) (Spec.map (CommRingCat.ofHom f))
      (AlgebraicGeometry.tilde N) hMap inferInstance hTilde p) →
      Nonempty (Module.Devissage.Complete A S M p) := sorry

/-- For a finite-type ring map and a finite module, complete dévissages of the associated
affine module sheaf at an ambient point exist exactly when complete algebraic dévissages
exist at the corresponding prime. -/
theorem exists_completeDevissageAt_tilde_iff
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (hf : f.FiniteType)
    (N : ModuleCat.{u} B) [Module.Finite B N]
    (p : PrimeSpectrum A) (q : PrimeSpectrum B) (hq : PrimeSpectrum.comap f q = p) :
    let S : FGAlgCat.{u} A := ⟨@CommAlgCat.of A _ B _ f.toAlgebra, hf⟩
    let M : FGModuleCat.{u} S.obj := ⟨N, (ModuleCat.isFG_iff N).2 inferInstance⟩
    let hMap : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom f)) :=
      HasRingHomProperty.Spec_iff.mpr hf
    let hTilde :=
      (@Scheme.Modules.tilde_isFiniteType_iff_module_finite (CommRingCat.of B) N).mpr
        (inferInstance : Module.Finite B N)
    Nonempty (@CompleteDevissageAtAmbientPoint
      (Spec (.of A)) (Spec (.of B)) (Spec.map (CommRingCat.ofHom f))
      (AlgebraicGeometry.tilde N) hMap inferInstance hTilde q) ↔
      Nonempty (Module.Devissage.CompleteAt A S M p q
        ((congrArg PrimeSpectrum.asIdeal hq).symm :
          p.asIdeal = q.asIdeal.comap f)) := sorry

end ModuleCat
