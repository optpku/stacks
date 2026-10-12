/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import ReasLib.CategoryTheory.Homology.DegreewiseSplit
public import ReasLib.CategoryTheory.ShortComplex.Admissible

@[expose] public section

/-!
# Admissibility for Homological Complexes

This leaf relates relative admissibility for the canonical functor which
forgets differentials to termwise split morphisms and degreewise splittings.
It applies to arbitrary homological-complex shapes; cochain-complex and
differential-graded-module APIs are specializations.
-/

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace HomologicalComplex

section

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {ι : Type w} {c : ComplexShape ι}

/-- A morphism of homological complexes is admissibly monic for the canonical graded-forgetful
functor exactly when all of its components are split monomorphisms. -/
theorem isAdmissibleMono_forget_iff_termwiseSplitMono
    {K L : HomologicalComplex C c} (f : K ⟶ L) :
    IsAdmissibleMono (forget C c) f ↔ ∀ i : ι, IsSplitMono (f.f i) := sorry

/-- A morphism of homological complexes is admissibly epic for the canonical graded-forgetful
functor exactly when all of its components are split epimorphisms. -/
theorem isAdmissibleEpi_forget_iff_termwiseSplitEpi
    {K L : HomologicalComplex C c} (f : K ⟶ L) :
    IsAdmissibleEpi (forget C c) f ↔ ∀ i : ι, IsSplitEpi (f.f i) := sorry

end

section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} {c : ComplexShape ι}

/-- A short complex of homological complexes is admissibly short exact for the canonical
graded-forgetful functor exactly when it admits a splitting after evaluation in every degree. -/
theorem isAdmissibleShortExact_forget_iff_nonempty_degreewiseSplitting
    (S : ShortComplex (HomologicalComplex C c)) :
    IsAdmissibleShortExact (forget C c) S ↔
      Nonempty (∀ i : ι, (ShortComplex.degreewise S i).Splitting) := sorry

end

end HomologicalComplex
