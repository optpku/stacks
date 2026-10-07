module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Retract
public import ReasLib.Algebra.Homology.HomologicalComplex.ObjectProperty

/-!
# Termwise finite-free retract complexes

This leaf specializes the generic `CochainComplex.termsIn` construction to module sheaves that
are retracts of finite free module sheaves.  Boundedness is deliberately owned separately.
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

/-- The object property of complexes that are termwise finite-free retracts. -/
def termwiseFiniteFreeRetract :
    ObjectProperty (_root_.CochainComplex (SheafOfModules.{w} R) ℤ) :=
  _root_.CochainComplex.termsIn (finiteFreeRetractModuleProperty R)

/-- A complex of `R`-modules is termwise a retract of finite free module sheaves. -/
abbrev IsTermwiseFiniteFreeRetract
    (E : _root_.CochainComplex (SheafOfModules.{w} R) ℤ) : Prop :=
  termwiseFiniteFreeRetract E

/-- Termwise finite-free retract complexes, as a full subcategory. -/
abbrev TermwiseFiniteFreeRetract :=
  (termwiseFiniteFreeRetract (R := R)).FullSubcategory

namespace TermwiseFiniteFreeRetract

/-- The canonical inclusion of termwise finite-free retract complexes. -/
abbrev ι : TermwiseFiniteFreeRetract (R := R) ⥤
    _root_.CochainComplex (SheafOfModules.{w} R) ℤ :=
  ObjectProperty.ι _

/-- Every term of a termwise finite-free retract complex lies in the finite-free retract
property. -/
theorem term_mem (E : TermwiseFiniteFreeRetract (R := R)) (i : ℤ) :
    finiteFreeRetractModuleProperty R (E.obj.X i) := sorry

end TermwiseFiniteFreeRetract

/-- Unfolding termwise finite-free retractness gives the degreewise retract-closure condition. -/
theorem isTermwiseFiniteFreeRetract_iff
    (E : _root_.CochainComplex (SheafOfModules.{w} R) ℤ) :
    IsTermwiseFiniteFreeRetract E ↔
      ∀ i : ℤ, finiteFreeRetractModuleProperty R (E.X i) := sorry

/-- Each term of a termwise finite-free retract complex lies in the finite-free retract closure. -/
theorem IsTermwiseFiniteFreeRetract.term_retractClosure
    {E : _root_.CochainComplex (SheafOfModules.{w} R) ℤ}
    (hE : IsTermwiseFiniteFreeRetract E) (i : ℤ) :
    finiteFreeRetractModuleProperty R (E.X i) := sorry

/-- Each term of a termwise finite-free retract complex is a retract of a finite free module
sheaf. -/
theorem IsTermwiseFiniteFreeRetract.term_retract_free
    {E : _root_.CochainComplex (SheafOfModules.{w} R) ℤ}
    (hE : IsTermwiseFiniteFreeRetract E) (i : ℤ) :
    ∃ I : Type w, Finite I ∧
      Nonempty (Retract (E.X i) (free I : SheafOfModules.{w} R)) := sorry

end CochainComplex
end SheafOfModules
