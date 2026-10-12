/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Yoneda.Section.Naturality
public import ReasLib.CategoryTheory.Functor.Equivalence

/-!
# Explicit-cleavage based Yoneda equivalence

This file packages the explicit section and its natural comparisons as quasi-inverse and
equivalence data. Consumers that only need evaluation or its computations need not import it.
-/

@[expose] public section

universe uC vC uS vS

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]
variable {p : S ⥤ C}

namespace BasedCategory.Yoneda.sectionOfCleavage

/-- The cleavage section, together with its canonical unit and counit, is explicit
quasi-inverse data for based Yoneda evaluation. -/
@[stacks 004B "explicit-cleavage based Yoneda quasi-inverse"]
noncomputable def quasiInverse [Functor.IsFibered.InGroupoids p]
    (χ : p.Cleavage) (U : C) : Functor.QuasiInverse (BasedCategory.Yoneda.evaluation p U) where
  inverse := sectionOfCleavage χ U
  unitIso := unitIso χ U
  counitIso := counitIso χ U

/-- The inverse stored by the explicit-cleavage based Yoneda quasi-inverse is the supplied
cleavage section. -/
@[simp]
theorem quasiInverse.inverse [Functor.IsFibered.InGroupoids p]
    (χ : p.Cleavage) (U : C) :
    (quasiInverse χ U).inverse = sectionOfCleavage χ U := sorry

/-- The unit stored by the explicit-cleavage based Yoneda quasi-inverse is the named unit. -/
@[simp]
theorem quasiInverse.unitIso [Functor.IsFibered.InGroupoids p]
    (χ : p.Cleavage) (U : C) :
    (quasiInverse χ U).unitIso = unitIso χ U := sorry

/-- The counit stored by the explicit-cleavage based Yoneda quasi-inverse is the named
counit. -/
@[simp]
theorem quasiInverse.counitIso [Functor.IsFibered.InGroupoids p]
    (χ : p.Cleavage) (U : C) :
    (quasiInverse χ U).counitIso = counitIso χ U := sorry

/-- The based Yoneda equivalence with inverse given by the supplied cleavage section. -/
@[stacks 004B "explicit-cleavage based Yoneda equivalence"]
noncomputable def equivalence [Functor.IsFibered.InGroupoids p]
    (χ : p.Cleavage) (U : C) : BasedCategory.Yoneda.hom p U ≌ p.Fiber U :=
  (quasiInverse χ U).adjointifyUnit

/-- The forward functor of the explicit-cleavage based Yoneda equivalence is evaluation. -/
@[simp]
theorem equivalence.functor [Functor.IsFibered.InGroupoids p]
    (χ : p.Cleavage) (U : C) :
    (equivalence χ U).functor = BasedCategory.Yoneda.evaluation p U := sorry

/-- The inverse retained by the based Yoneda equivalence is the supplied cleavage section. -/
@[simp]
theorem equivalence.inverse [Functor.IsFibered.InGroupoids p]
    (χ : p.Cleavage) (U : C) :
    (equivalence χ U).inverse = sectionOfCleavage χ U := sorry

/-- The counit retained by the based Yoneda equivalence is the explicit-cleavage counit. -/
@[simp]
theorem equivalence.counitIso [Functor.IsFibered.InGroupoids p]
    (χ : p.Cleavage) (U : C) :
    (equivalence χ U).counitIso = counitIso χ U := sorry

end BasedCategory.Yoneda.sectionOfCleavage

end CategoryTheory
