/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.Isom
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 99.16.5: in Situation 99.16.3, the diagonal of the category of
complexes is representable by algebraic spaces. Equivalently, every fibrewise
Isom presheaf is represented by an algebraic space over its test scheme,
with the universe lift required by the Hom-universe of complexes. -/
@[stacks 0DLG] #check
  (AlgebraicGeometry.AlgebraicSpace.Complexes.isom_isAlgebraicSpace :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
      [AlgebraicSpace.Proper f] [AlgebraicSpace.Flat f]
      [AlgebraicSpace.FinitePresentation f],
      AlgebraicGeometry.AlgebraicSpace.Complexes.isAlgebraicSpace f)
