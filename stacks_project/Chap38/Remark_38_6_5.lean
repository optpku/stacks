/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.CompleteDevissage.Affine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace ModuleCat

/- Remark 38.6.5 (1): for a finite-type map `f : A →+* B`, a finite `B`-module `N`,
and `q ∈ Spec(B)` lying over `p ∈ Spec(A)`, existence of a complete dévissage of
`Ñ/Spec(B)/Spec(A)` over `p` implies existence of a complete algebraic dévissage of
`N/B/A` over `p`. The converse is not asserted because the latter notion omits the
relative-dimension condition. -/
@[stacks 05I0] #check
  (ModuleCat.exists_completeDevissageOver_of_tilde :
    ∀ {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (hf : f.FiniteType)
      (N : ModuleCat.{u} B) [Module.Finite B N]
      (p : PrimeSpectrum A) (q : PrimeSpectrum B) (hq : PrimeSpectrum.comap f q = p),
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
      Nonempty (Module.Devissage.Complete A S M p))

/- Remark 38.6.5 (2): in the same affine situation, existence of a complete dévissage of
`Ñ/Spec(B)/Spec(A)` at `q` is equivalent to existence of a complete algebraic dévissage
of `N/B/A` at `q`; both at-point notions include the relative-dimension condition. -/
@[stacks 05I0] #check
  (ModuleCat.exists_completeDevissageAt_tilde_iff :
    ∀ {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (hf : f.FiniteType)
      (N : ModuleCat.{u} B) [Module.Finite B N]
      (p : PrimeSpectrum A) (q : PrimeSpectrum B) (hq : PrimeSpectrum.comap f q = p),
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
          p.asIdeal = q.asIdeal.comap f)))

end ModuleCat
