/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Fiber

open CategoryTheory

universe u

/- Lemma 29.36.7 (1): a scheme over a field is étale over that field if and only if it is a
disjoint union of spectra of finite separable field extensions. -/
@[stacks 02GL] #check
  (AlgebraicGeometry.etale_iff_schemeAsDisjointUnionOfSpecFiniteSeparable :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k),
      AlgebraicGeometry.Etale X.hom ↔
        Nonempty
          (AlgebraicGeometry.SchemeAsDisjointUnionOfSpecFiniteSeparable k X))

/- Lemma 29.36.7 (2): every fibre of an étale morphism is a disjoint union of spectra of finite
separable extensions of the corresponding residue field. -/
@[stacks 02GL] #check
  (AlgebraicGeometry.fiber_schemeAsDisjointUnionOfSpecFiniteSeparable_of_etale :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.Etale f] (s : S),
      Nonempty
        (AlgebraicGeometry.SchemeAsDisjointUnionOfSpecFiniteSeparable (S.residueField s)
          (Over.mk (f.fiberOverSpecResidueField s).hom)))
