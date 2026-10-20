/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszlo.Affine

/-!
# Lemma 81.12.2

For a Beauville–Laszlo glueing pair, the canonical functor
`Over (space R) ⥤ category R' f` restricts to an equivalence between affine
glueable algebraic spaces over `X` and affine objects of
`Spaces(U ← U' → X')`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing

noncomputable section

universe u

/- Lemma 81.12.2: for a glueing pair, the canonical functor restricts to an
equivalence between affine glueable algebraic spaces over the base and triples
whose three components are affine. -/
@[stacks 0F9Q] #check
  (AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing.affineGlueableFunctor_isEquivalence :
    {R R' : Type u} → [CommRing R] → [CommRing R'] → [Algebra R R'] → (f : R) →
      [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f] →
      (AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing.affineGlueableFunctor R' f).IsEquivalence)
