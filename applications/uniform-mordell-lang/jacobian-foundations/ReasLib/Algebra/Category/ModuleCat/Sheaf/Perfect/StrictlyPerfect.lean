module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Perfect.Termwise
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Termwise

/-!
# Strictly perfect complexes of module sheaves

Strict perfectness is the generic bounded-termwise construction specialized to the object
property of being a retract of a finite free module sheaf.  The `ObjectProperty` and its full
subcategory are the canonical owners; the predicate-facing abbreviation keeps theorem surfaces
close to ordinary mathematical language.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace SheafOfModules
namespace CochainComplex

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable {R : Sheaf J RingCat.{w}}

/-- The object property of bounded complexes whose terms are retracts of finite free module
sheaves. -/
@[stacks 08C4]
def strictlyPerfect : ObjectProperty (_root_.CochainComplex (SheafOfModules.{w} R) ℤ) :=
  _root_.CochainComplex.boundedTermsIn (finiteFreeRetractModuleProperty R)

/-- A complex is strictly perfect when it belongs to `strictlyPerfect`. -/
abbrev IsStrictlyPerfect
    (E : _root_.CochainComplex (SheafOfModules.{w} R) ℤ) : Prop :=
  strictlyPerfect E

/-- Strictly perfect complexes, as a full subcategory. -/
abbrev StrictlyPerfect :=
  (strictlyPerfect (R := R)).FullSubcategory

namespace StrictlyPerfect

/-- The canonical inclusion of strictly perfect complexes. -/
abbrev ι : StrictlyPerfect (R := R) ⥤
    _root_.CochainComplex (SheafOfModules.{w} R) ℤ :=
  ObjectProperty.ι _

/-- The underlying complex of a strictly perfect complex is bounded. -/
theorem bounded (E : StrictlyPerfect (R := R)) :
    _root_.CochainComplex.bounded (SheafOfModules.{w} R) E.obj := sorry

/-- Every term of a strictly perfect complex lies in the finite-free retract property. -/
theorem term_mem (E : StrictlyPerfect (R := R)) (i : ℤ) :
    finiteFreeRetractModuleProperty R (E.obj.X i) := sorry

end StrictlyPerfect

/-- Strict perfectness is explicit boundedness together with termwise finite-free retractness. -/
theorem isStrictlyPerfect_iff
    (E : _root_.CochainComplex (SheafOfModules.{w} R) ℤ) :
    IsStrictlyPerfect E ↔
      (∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b) ∧
        IsTermwiseFiniteFreeRetract E := sorry

/-- Strict perfectness is equivalent to the fully expanded degreewise finite-free retract
condition. -/
theorem isStrictlyPerfect_iff_explicit
    (E : _root_.CochainComplex (SheafOfModules.{w} R) ℤ) :
    IsStrictlyPerfect E ↔
      (∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b) ∧
        ∀ i : ℤ, finiteFreeRetractModuleProperty R (E.X i) := sorry

/-- Strict perfectness is canonical boundedness together with termwise finite-free retractness. -/
theorem isStrictlyPerfect_iff_bounded_and_termwiseFiniteFreeRetract
    (E : _root_.CochainComplex (SheafOfModules.{w} R) ℤ) :
    IsStrictlyPerfect E ↔
      _root_.CochainComplex.bounded (SheafOfModules.{w} R) E ∧
        IsTermwiseFiniteFreeRetract E := sorry

/-- A strictly perfect complex has explicit lower and upper bounds. -/
theorem IsStrictlyPerfect.bounded
    {E : _root_.CochainComplex (SheafOfModules.{w} R) ℤ}
    (hE : IsStrictlyPerfect E) :
    ∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b := sorry

/-- A strictly perfect complex belongs to the canonical bounded object property. -/
theorem IsStrictlyPerfect.boundedProperty
    {E : _root_.CochainComplex (SheafOfModules.{w} R) ℤ}
    (hE : IsStrictlyPerfect E) :
    _root_.CochainComplex.bounded (SheafOfModules.{w} R) E := sorry

/-- A strictly perfect complex is termwise finite-free retract. -/
theorem IsStrictlyPerfect.termwiseFiniteFreeRetract
    {E : _root_.CochainComplex (SheafOfModules.{w} R) ℤ}
    (hE : IsStrictlyPerfect E) :
    IsTermwiseFiniteFreeRetract E := sorry

/-- Each term of a strictly perfect complex lies in the finite-free retract closure. -/
theorem IsStrictlyPerfect.term_retractClosure
    {E : _root_.CochainComplex (SheafOfModules.{w} R) ℤ}
    (hE : IsStrictlyPerfect E) (i : ℤ) :
    finiteFreeRetractModuleProperty R (E.X i) := sorry

/-- Each term of a strictly perfect complex is a retract of a finite free module sheaf. -/
theorem IsStrictlyPerfect.term_retract_free
    {E : _root_.CochainComplex (SheafOfModules.{w} R) ℤ}
    (hE : IsStrictlyPerfect E) (i : ℤ) :
    ∃ I : Type w, Finite I ∧
      Nonempty (Retract (E.X i) (free I : SheafOfModules.{w} R)) := sorry

/-- A bounded complex with termwise finite-free retract terms is strictly perfect. -/
theorem isStrictlyPerfect_of_bounded_of_termwiseFiniteFreeRetract
    {E : _root_.CochainComplex (SheafOfModules.{w} R) ℤ}
    (hbounded : _root_.CochainComplex.bounded (SheafOfModules.{w} R) E)
    (hterms : IsTermwiseFiniteFreeRetract E) :
    IsStrictlyPerfect E := sorry

/-- Explicit bounds and degreewise finite-free retract closure assemble into a strictly perfect
complex. -/
theorem isStrictlyPerfect_of_bounds_of_term_retractClosure
    {E : _root_.CochainComplex (SheafOfModules.{w} R) ℤ}
    (hbounded : ∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b)
    (hterms : ∀ i : ℤ, finiteFreeRetractModuleProperty R (E.X i)) :
    IsStrictlyPerfect E := sorry

end CochainComplex
end SheafOfModules
