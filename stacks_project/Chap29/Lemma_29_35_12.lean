/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Fiber
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 29.35.12 (1): an unramified morphism induces a finite separable extension of residue
fields at every point. -/
@[stacks 02G8] #check
  (AlgebraicGeometry.residueField_finite_separable_of_unramified :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Unramified f] (x : X),
      FiniteDimensional (S.residueField (f x)) (X.residueField x) ∧
        Algebra.IsSeparable (S.residueField (f x)) (X.residueField x))

/- Lemma 29.35.12 (2): a locally finite type morphism whose fibres are disjoint unions of spectra
of finite separable residue-field extensions is unramified. -/
@[stacks 02G8] #check
  (AlgebraicGeometry.unramified_of_fiber_schemeAsDisjointUnionOfSpecFiniteSeparable :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f],
      f.FibersAreDisjointUnionOfSpecFiniteSeparable → Unramified f)

/- Lemma 29.35.12 (3): a locally finite presentation morphism whose fibres are disjoint unions
of spectra of finite separable residue-field extensions is G-unramified. -/
@[stacks 02G8] #check
  (AlgebraicGeometry.gUnramified_of_fiber_schemeAsDisjointUnionOfSpecFiniteSeparable :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f],
      f.FibersAreDisjointUnionOfSpecFiniteSeparable → GUnramified f)
