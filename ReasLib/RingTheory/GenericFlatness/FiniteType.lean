/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.GenericFlatness.Localization

/-!
# Generic flatness over finite-type algebras

For a finite-type algebra over a domain and a finite module, a suitable nonzero
principal localization makes the algebra and module free over the localized
base while retaining finite-presentation properties. Variants cover Noetherian
bases and finite-presentation hypotheses.
-/

@[expose] public section

universe u v w

namespace GenericFlatness

/-- If `R` is a domain, `R → S` is of finite type, and `M` is a finite `S`-module,
then there is a nonzero `f : R` for which `S_f` and `M_f` are free over `R_f`, `S_f`
is finitely presented over `R_f`, and `M_f` is finitely presented over `S_f`. -/
@[stacks 051T "generic freeness over a finite type algebra"]
theorem exists_nonzero_away_of_finiteType
    {R : Type u} [CommRing R] [IsDomain R]
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    {M : Type w} [AddCommGroup M] [Module S M] [Module.Finite S M] :
    ∃ f : R, f ≠ 0 ∧ LocalizationCondition R S M f := sorry

/-- Over a Noetherian domain, a finite-type algebra and finite module have a nonzero
principal localization on which the module is free over the localized base. -/
@[stacks 051R "Noetherian generic freeness module clause"]
theorem exists_nonzero_away_module_free
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    {M : Type w} [AddCommGroup M] [Module S M] [Module.Finite S M] :
    ∃ f : R, f ≠ 0 ∧
      -- Local instance justification (instance diamond): use the relative `R_f`-module action
      -- induced by `R → S` without registering it as a global target instance.
      letI : Module (Localization.Away f)
          (LocalizedModule.Away (algebraMap R S f) M) :=
        Localization.Away.Relative.algebraMapModule f
      Module.Free (Localization.Away f)
        (LocalizedModule.Away (algebraMap R S f) M) := sorry

/-- Finite-presentation hypotheses give a nonzero localization on which the module is free,
without a Noetherian assumption on the domain. -/
@[stacks 051S "finite-presentation generic freeness module clause"]
theorem exists_nonzero_away_module_free_of_finitePresentation
    {R : Type u} [CommRing R] [IsDomain R]
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    {M : Type w} [AddCommGroup M] [Module S M]
    [Module.FinitePresentation S M] :
    ∃ f : R, f ≠ 0 ∧
      -- Local instance justification (instance diamond): use the named relative action on the
      -- localized module rather than registering a competing ambient `R_f` action.
      letI : Module (Localization.Away f)
          (LocalizedModule.Away (algebraMap R S f) M) :=
        Localization.Away.Relative.algebraMapModule f
      Module.Free (Localization.Away f)
        (LocalizedModule.Away (algebraMap R S f) M) := sorry

end GenericFlatness
