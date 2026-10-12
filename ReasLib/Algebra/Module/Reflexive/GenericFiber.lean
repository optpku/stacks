/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Reflexive
public import ReasLib.Algebra.Module.LocalizedModule.Quotient

/-!
# Generic fibers of reflexive hulls

This leaf compares a finite module, its double dual, and its quotient by torsion after passing to
the fraction-field localization of a domain.

@stack 0AVC
-/

@[expose] public section

open Module
open LocalizedModule (map mkLinearMap)
open scoped nonZeroDivisors

universe u v

namespace Module.Dual

/-- The localization of the double-dual evaluation map of a finite module at the generic point
is bijective. -/
@[stacks 0AVC "generic localization of double-dual evaluation"]
theorem genericLocalization_map_eval_bijective
    {R : Type u} [CommRing R] [IsDomain R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Function.Bijective (map R⁰ (eval R M)) := sorry

end Module.Dual

namespace Module

/-- The quotient by torsion induces a bijection on the generic localizations of a finite module. -/
@[stacks 0AVC "generic localization of the torsion quotient"]
theorem genericLocalization_map_torsionQuotient_bijective
    {R : Type u} [CommRing R] [IsDomain R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Function.Bijective (map R⁰ (Submodule.torsion R M).mkQ) := sorry

end Module

namespace Module.Dual

/-- The comparison from the double dual of a finite module to the generic localization of its
quotient by torsion, parametrized by explicit proofs that the two canonical localized maps are
bijective.  The proof parameters keep the non-Prop map data free of theorem-level `sorryAx`. -/
@[stacks 0AVC "double dual in the torsion-free generic fiber"]
noncomputable def toTorsionQuotientGenericLocalizationOf
    {R : Type u} [CommRing R] [IsDomain R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (heval : Function.Bijective (map R⁰ (eval R M)))
    (hquot : Function.Bijective (map R⁰ (Submodule.torsion R M).mkQ)) :
    Dual R (Dual R M) →ₗ[R] LocalizedModule R⁰ (M ⧸ Submodule.torsion R M) :=
  let evalEquiv :
      LocalizedModule R⁰ M ≃ₗ[Localization R⁰]
        LocalizedModule R⁰ (Dual R (Dual R M)) :=
    LinearEquiv.ofBijective (map R⁰ (eval R M)) heval
  let torsionQuotientEquiv :
      LocalizedModule R⁰ M ≃ₗ[Localization R⁰]
        LocalizedModule R⁰ (M ⧸ Submodule.torsion R M) :=
    LinearEquiv.ofBijective (map R⁰ (Submodule.torsion R M).mkQ) hquot
  (LinearMap.restrictScalars R torsionQuotientEquiv.toLinearMap).comp
    ((LinearMap.restrictScalars R evalEquiv.symm.toLinearMap).comp
      (mkLinearMap R⁰ (Dual R (Dual R M))))

/-- The generic-fiber comparison extends the quotient map along double-dual evaluation. -/
@[stacks 0AVC "double dual generic-fiber comparison specification"]
theorem toTorsionQuotientGenericLocalizationOf_comp_eval
    {R : Type u} [CommRing R] [IsDomain R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (heval : Function.Bijective (map R⁰ (eval R M)))
    (hquot : Function.Bijective (map R⁰ (Submodule.torsion R M).mkQ)) :
    (toTorsionQuotientGenericLocalizationOf heval hquot).comp (eval R M) =
      (mkLinearMap R⁰ (M ⧸ Submodule.torsion R M)).comp
        (Submodule.torsion R M).mkQ := sorry

/-- The specification on the evaluation image uniquely determines the generic-fiber comparison. -/
@[stacks 0AVC "double dual generic-fiber comparison uniqueness"]
theorem toTorsionQuotientGenericLocalizationOf_unique
    {R : Type u} [CommRing R] [IsDomain R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (heval : Function.Bijective (map R⁰ (eval R M)))
    (hquot : Function.Bijective (map R⁰ (Submodule.torsion R M).mkQ))
    (f : Dual R (Dual R M) →ₗ[R] LocalizedModule R⁰ (M ⧸ Submodule.torsion R M))
    (hf : f.comp (eval R M) =
      (mkLinearMap R⁰ (M ⧸ Submodule.torsion R M)).comp
        (Submodule.torsion R M).mkQ) :
    f = toTorsionQuotientGenericLocalizationOf heval hquot := sorry

/-- The proof-parametric generic-fiber comparison is independent of the supplied bijectivity
proofs. -/
@[stacks 0AVC "double dual generic-fiber comparison proof independence"]
theorem toTorsionQuotientGenericLocalizationOf_congr
    {R : Type u} [CommRing R] [IsDomain R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (heval heval' : Function.Bijective (map R⁰ (eval R M)))
    (hquot hquot' : Function.Bijective (map R⁰ (Submodule.torsion R M).mkQ)) :
    toTorsionQuotientGenericLocalizationOf heval hquot =
      toTorsionQuotientGenericLocalizationOf heval' hquot' := sorry

end Module.Dual
