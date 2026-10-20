/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Fiber
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 29.35.11 (1): a scheme over a field is unramified if and only if it is a disjoint union
of spectra of finite separable field extensions. -/
@[stacks 02G7]
#check
  (AlgebraicGeometry.unramified_iff_schemeAsDisjointUnionOfSpecFiniteSeparable :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k),
      AlgebraicGeometry.Unramified X.hom ↔
        Nonempty (AlgebraicGeometry.SchemeAsDisjointUnionOfSpecFiniteSeparable k X))

/- Lemma 29.35.11 (2): every fibre of an unramified morphism is a disjoint union of spectra of
finite separable extensions of the corresponding residue field. -/
@[stacks 02G7]
#check
  (AlgebraicGeometry.fiber_schemeAsDisjointUnionOfSpecFiniteSeparable_of_unramified :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.Unramified f]
      (s : S),
      Nonempty
        (AlgebraicGeometry.SchemeAsDisjointUnionOfSpecFiniteSeparable (S.residueField s)
          (Over.mk (f.fiberOverSpecResidueField s).hom)))
