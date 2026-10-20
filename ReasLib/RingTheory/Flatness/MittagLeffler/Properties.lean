/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flatness.MittagLeffler

@[expose] public section

/-!
# Basic Mittag-Leffler Module Constructions

This leaf supplies the canonical one-object Mittag-Leffler presentation of a finitely presented
module and the resulting instance. The predicate and presentation data themselves live in the
lighter `ReasLib.RingTheory.Flatness.MittagLeffler` core.
-/

open CategoryTheory CategoryTheory.Limits

universe u v

noncomputable section

namespace Module.MittagLeffler.Presentation

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The canonical one-object presentation of a finitely presented module is a
Mittag-Leffler directed system. -/
@[stacks 059F "finite presentation criterion"]
theorem self_isMittagLeffler [Module.FinitePresentation R M] :
    IsMittagLefflerDirectedSystem
      ((ColimitPresentation.self
        (ModuleCat.of.{max u v} R (ULift.{max u v} M)) :
        ColimitPresentation PUnit.{max u v + 1}
          (ModuleCat.of.{max u v} R (ULift.{max u v} M))).diag) := by
  letI : Module.FinitePresentation R (ULift.{max u v} M) :=
    Module.FinitePresentation.of_equiv ULift.moduleEquiv.symm
  constructor
  · intro i
    change Module.FinitePresentation R (ULift.{max u v} M)
    infer_instance
  · intro N
    apply CategoryTheory.Functor.isMittagLeffler_of_surjective
    intro i j f
    have hij : i = j := Subsingleton.elim _ _
    subst j
    rw [Subsingleton.elim f (𝟙 _)]
    intro g
    refine ⟨g, ?_⟩
    change (𝟙 _) ≫ g = g
    simp

/-- The canonical one-object Mittag-Leffler presentation of a finitely presented module. -/
@[stacks 059F "finite presentation"]
noncomputable def ofFinitePresentation [Module.FinitePresentation R M] :
    Module.MittagLeffler.Presentation.{u, v, max u v} R M :=
  Presentation.ofColimit
    (ColimitPresentation.self
      (ModuleCat.of.{max u v} R (ULift.{max u v} M)) :
      ColimitPresentation PUnit.{max u v + 1}
        (ModuleCat.of.{max u v} R (ULift.{max u v} M)))
    (self_isMittagLeffler (R := R) (M := M))

end Module.MittagLeffler.Presentation

namespace Module.MittagLeffler

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Every finitely presented module is Mittag-Leffler. -/
@[stacks 059F "finite presentation instance"]
instance ofFinitePresentation [Module.FinitePresentation R M] :
    Module.MittagLeffler R M :=
  Presentation.ofFinitePresentation.toMittagLeffler

end Module.MittagLeffler
