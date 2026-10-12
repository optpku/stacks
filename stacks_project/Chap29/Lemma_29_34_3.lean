/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import StacksCheckRecall

/-!
# Lemma 29.34.3

A flat morphism, locally of finite presentation, is smooth when all of its fibers are smooth.

@stack 01V8
-/

@[expose] public section

universe u

/- Lemma 29.34.3

A flat morphism, locally of finite presentation, is smooth when all of its fibers are smooth.
-/
@[stacks 01V8] #check
  (@AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.LocallyOfFinitePresentation f] [AlgebraicGeometry.Flat f],
      (∀ s, AlgebraicGeometry.Smooth (f.fiberToSpecResidueField s)) →
        AlgebraicGeometry.Smooth f)
