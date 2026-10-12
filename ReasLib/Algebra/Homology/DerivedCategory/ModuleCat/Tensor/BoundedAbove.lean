/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Above.Basic

@[expose] public section

/-!
# Bounded-above derived tensor existence

@stack 064G
@stack 064H

This leaf records only the canonical `HasLeftDerivedFunctor` predicates for fixed-factor tensor
and extension of scalars. It deliberately does not select the resulting total derived functors
until their existence proofs are free of placeholders.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u v

namespace ModuleCat.BoundedAbove

/-- Bounded-above tensoring with a fixed module admits a total left derived functor. -/
@[stacks 064G "bounded-above fixed-factor derived tensor existence"]
theorem tensorRight_hasLeftDerived
    {R : Type u} [CommRing R] (M : ModuleCat R) :
    (tensorRight M).toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso (ModuleCat R)) := sorry

/-- Bounded-above extension of scalars admits a total left derived functor. -/
@[stacks 064H "bounded-above derived extension-of-scalars existence"]
theorem extendScalars_hasLeftDerived
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A] :
    (ModuleCat.extendScalars (algebraMap R A)).toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso (ModuleCat R)) := sorry

end ModuleCat.BoundedAbove
