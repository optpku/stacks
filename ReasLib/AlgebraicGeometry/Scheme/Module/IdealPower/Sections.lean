/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Hom
public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Quotient

/-!
# Sections on affine ideal complements

This file states the injectivity and isomorphism properties of the canonical comparisons from
ideal-power Hom colimits to sections of a tilde module on an ideal complement.
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {A : Type u} [CommRing A]

/-- For a finitely generated ideal, the canonical comparison from the ideal-power Hom colimit to
sections on its complement is injective. -/
theorem idealPowerHomColimitToComplementSections_injective
    (I : Ideal A) (hI : I.FG) (M : ModuleCat A) :
    Function.Injective
      (idealPowerHomColimitToComplementSections I hI M).hom := sorry

/-- The canonical comparison from the quotient ideal-power Hom colimit to sections on the ideal
complement is an isomorphism. -/
theorem isIso_idealPowerQuotientHomColimitToComplementSections
    (I : Ideal A) (hI : I.FG) (M : ModuleCat A) :
    IsIso (idealPowerQuotientHomColimitToComplementSections I hI M) := sorry

namespace idealPowerHomColimitToComplementSections

/-- If the first ideal-power annihilated submodule vanishes, the canonical comparison from the
unquotiented ideal-power Hom colimit to complement sections is an isomorphism. -/
theorem isIso_of_powerAnnihilatedSubmodule_eq_bot
    (I : Ideal A) (hI : I.FG) (M : ModuleCat A)
    (hM : I.powerAnnihilatedSubmodule M 1 = ⊥) :
    IsIso (idealPowerHomColimitToComplementSections I hI M) := sorry

end idealPowerHomColimitToComplementSections

/-- If every module element annihilated by every member of the ideal is zero, the canonical
comparison from the ideal-power Hom colimit to complement sections is an isomorphism. -/
theorem isIso_idealPowerHomColimitToComplementSections_of_annihilatorCondition
    (I : Ideal A) (hI : I.FG) (M : ModuleCat A)
    (hM : ∀ x : M, (∀ a : A, a ∈ I → a • x = 0) → x = 0) :
    IsIso (idealPowerHomColimitToComplementSections I hI M) := sorry

end AlgebraicGeometry.Scheme.Modules
