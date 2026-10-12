/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import ReasLib.CategoryTheory.Adjunction.HomologicalComplex
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# K-Injectivity Under Exact Adjunctions

@stack 08BJ

This leaf specializes the neutral exact-adjunction complex map to the
K-injective condition.  It does not impose global additive instances: those
are already packaged by `Adjunction.Exact.mapHomologicalComplex`.
-/

open CategoryTheory
open ComplexShape

universe uA uB vA vB

namespace CochainComplex.IsKInjective

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B] [Abelian A] [Abelian B]
  {u : A ⥤ B} {v : B ⥤ A}

/-- The right adjoint of an exact functor sends K-injective
cochain complexes to K-injective cochain complexes. -/
@[stacks 08BJ]
theorem map_of_exactLeftAdjoint
    (I : CochainComplex A ℤ) [I.IsKInjective]
    (adj : v ⊣ u) (h_exact : exactFunctor B A v) :
    CochainComplex.IsKInjective
      ((CategoryTheory.Adjunction.Exact.mapHomologicalComplex adj h_exact
        (up ℤ)).obj I) := sorry

/-- With an ambient additive instance, the standard termwise complex map of the right adjoint
sends K-injective cochain complexes to K-injective cochain complexes. -/
@[stacks 08BJ]
theorem mapHomologicalComplex_of_exactLeftAdjoint
    (I : CochainComplex A ℤ) [I.IsKInjective]
    (adj : v ⊣ u) (h_exact : exactFunctor B A v) [u.Additive] :
    CochainComplex.IsKInjective ((u.mapHomologicalComplex (up ℤ)).obj I) := sorry

end CochainComplex.IsKInjective
