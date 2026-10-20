/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.Degeneration
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Characterization
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.PageTwo
import Mathlib.Tactic.CrossRefAttribute

/-!
# Single-column degeneration for truncation right-derived spectral sequences

The truncation realization gives a reusable bounded-below comparison whenever every cohomology
object of the input is right-acyclic away from degree zero.  The bounded-below hypothesis is kept
explicit because it is the convergence input; it is not hidden in a local instance or a stronger
global boundedness assumption.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

namespace Realization

/-- A bounded truncation realization with acyclic cohomology objects identifies its abutment
cohomology with the degree-zero right-derived functor of the corresponding cohomology object. -/
@[stacks 012U "single-column degeneration of a truncation realization"]
theorem cohomology_isomorphic_rightDerived_zero_of_vanishes
    {K : DerivedCategory A} (S : Realization F K)
    (hK : DerivedCategory.IsBoundedBelow K)
    (hvanish : ∀ j : ℤ,
      Functor.RightDerived.Vanishes.aboveZero F
        ((DerivedCategory.homologyFunctor A j).obj K)) (q : ℤ) :
    IsIsomorphic
      ((Functor.RightDerived.Homotopy.cohomologyFunctor F q).obj K)
      ((F.rightDerived 0).obj ((DerivedCategory.homologyFunctor A q).obj K)) := sorry

end Realization

/-- A bounded-below derived object whose cohomology objects are right-acyclic has hypercohomology
given by the degree-zero right-derived functor of each cohomology object. -/
@[stacks 012U "bounded-below right-derived single-column degeneration"]
theorem cohomology_isomorphic_rightDerived_zero_of_vanishes
    [IsGrothendieckAbelian.{wA} A]
    {K : DerivedCategory A} (hK : DerivedCategory.IsBoundedBelow K)
    (hvanish : ∀ j : ℤ,
      Functor.RightDerived.Vanishes.aboveZero F
        ((DerivedCategory.homologyFunctor A j).obj K)) (q : ℤ) :
    IsIsomorphic
      ((Functor.RightDerived.Homotopy.cohomologyFunctor F q).obj K)
      ((F.rightDerived 0).obj ((DerivedCategory.homologyFunctor A q).obj K)) := sorry

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation

end
