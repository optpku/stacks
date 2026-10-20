/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Localization.Away.Relative

/-!
# Localization conditions for generic flatness

`LocalizationCondition R S M f` records finite-presentation and finite-free
properties of an algebra and module after principal localization at `f`.  It is
an ordinary proposition rather than a typeclass because the condition depends
on the chosen principal open.
-/

@[expose] public section

universe u v w z

namespace GenericFlatness

/- The `R_f` actions below are fixed to the maps induced by `R → S`.  Keeping them local to the
field types prevents these non-native actions from competing with canonical localization instances.
-/

/-- The generic-flatness localization condition at `f`: `S_f` and `M_f` are finitely presented
in the indicated senses and are free over `R_f`. -/
@[stacks 051T "generic-flatness localization condition"]
structure LocalizationCondition
    (R : Type u) [CommSemiring R]
    (S : Type v) [CommSemiring S] [Algebra R S]
    (M : Type w) [AddCommMonoid M] [Module S M]
    (f : R) : Prop where
  /-- The localized algebra is finitely presented over the base localization. -/
  finitePresentationAlgebra :
    -- Local instance justification (instance diamond): use the relative algebra action induced by
    -- `R → S`, which may compete with another ambient action on the target localization.
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
      Localization.Away.Relative.algebraMapAlgebra f
    Algebra.FinitePresentation (Localization.Away f) (Localization.Away (algebraMap R S f))
  /-- The localized module is finitely presented over the localized target algebra. -/
  finitePresentationModule :
    Module.FinitePresentation (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M)
  /-- The localized target algebra is free over the base localization. -/
  freeAlgebra :
    -- Local instance justification (instance diamond): use the relative algebra action induced by
    -- `R → S`, which may compete with another ambient action on the target localization.
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
      Localization.Away.Relative.algebraMapAlgebra f
    Module.Free (Localization.Away f) (Localization.Away (algebraMap R S f))
  /-- The localized module is free over the base localization. -/
  freeModule :
    -- Local instance justification (instance diamond): use the relative module action induced by
    -- `R → S`, which may compete with another ambient action on the localized module.
    letI : Module (Localization.Away f) (LocalizedModule.Away (algebraMap R S f) M) :=
      Localization.Away.Relative.algebraMapModule f
    Module.Free (Localization.Away f) (LocalizedModule.Away (algebraMap R S f) M)

/-- Use a localization condition in the local typeclass context determined by its canonical
principal-localization actions. -/
noncomputable def LocalizationCondition.withInstances
    {R : Type u} [CommSemiring R]
    {S : Type v} [CommSemiring S] [Algebra R S]
    {M : Type w} [AddCommMonoid M] [Module S M]
    {f : R} (h : LocalizationCondition R S M f)
    {P : Sort z}
    (k :
      -- Local instance justification (instance diamond): install the relative algebra action
      -- determined by `R → S` while evaluating the continuation.
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        Localization.Away.Relative.algebraMapAlgebra f
      -- Local instance justification (instance diamond): install the relative module action
      -- determined by `R → S` while evaluating the continuation.
      letI : Module (Localization.Away f) (LocalizedModule.Away (algebraMap R S f) M) :=
        Localization.Away.Relative.algebraMapModule f
      -- Local instance justification (instance diamond): install scalar compatibility for the
      -- selected relative algebra and module actions.
      letI : IsScalarTower (Localization.Away f)
          (Localization.Away (algebraMap R S f))
          (LocalizedModule.Away (algebraMap R S f) M) :=
        Localization.Away.Relative.mapModule_isScalarTower (algebraMap R S) f
      -- Local instance justification (proof-local temporary data): expose the algebra finite-
      -- presentation component of the condition only inside the continuation.
      letI : Algebra.FinitePresentation (Localization.Away f)
          (Localization.Away (algebraMap R S f)) := h.finitePresentationAlgebra
      -- Local instance justification (proof-local temporary data): expose the module finite-
      -- presentation component of the condition only inside the continuation.
      letI : Module.FinitePresentation (Localization.Away (algebraMap R S f))
          (LocalizedModule.Away (algebraMap R S f) M) := h.finitePresentationModule
      -- Local instance justification (proof-local temporary data): expose the algebra freeness
      -- component of the condition only inside the continuation.
      letI : Module.Free (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        h.freeAlgebra
      -- Local instance justification (proof-local temporary data): expose the module freeness
      -- component of the condition only inside the continuation.
      letI : Module.Free (Localization.Away f)
          (LocalizedModule.Away (algebraMap R S f) M) := h.freeModule
      P) : P :=
  k

/-- The generic-flatness condition after localizing the base, target, and module away from
`f`, evaluated at an arbitrary element of the localized base ring.  This fixes the unique
relative `R_f`-algebra structure on `S_f` without installing a global instance. -/
noncomputable abbrev LocalizationCondition.away
    {R : Type u} [CommSemiring R]
    {S : Type v} [CommSemiring S] [Algebra R S]
    {M : Type w} [AddCommMonoid M] [Module S M]
    (f : R) (u : Localization.Away f) : Prop :=
  -- Local instance justification (instance diamond): evaluate the localized condition using the
  -- relative algebra action determined by `R → S` rather than an unrelated ambient action.
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    Localization.Away.Relative.algebraMapAlgebra f
  LocalizationCondition (Localization.Away f)
    (Localization.Away (algebraMap R S f))
    (LocalizedModule.Away (algebraMap R S f) M) u

end GenericFlatness
