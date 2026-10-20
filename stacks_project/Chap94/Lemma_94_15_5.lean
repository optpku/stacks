/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.RepresentableSource
import StacksCheckRecall

/-!
# Sources of morphisms representable by algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/- Lemma 94.15.5 (1): let `S` be a scheme contained in `Sch_fppf`. Let
`f : X ⟶ Y` be a 1-morphism of categories fibred in groupoids over
`(Sch/S)_fppf`. Assume `f` is representable by algebraic spaces
(`hf : relativelyRepresentableByAlgebraicSpaces f`). If `Y` is a stack in
groupoids, then so is `X`. -/
@[stacks 05UN] #check
  (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.source_isStack :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
      (hf : relativelyRepresentableByAlgebraicSpaces f)
      [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p],
      IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p)

/- Lemma 94.15.5 (2): let `S` be a scheme contained in `Sch_fppf`. Let
`f : X ⟶ Y` be a 1-morphism of categories fibred in groupoids over
`(Sch/S)_fppf`. Assume `f` is representable by algebraic spaces
(`hf : relativelyRepresentableByAlgebraicSpaces f`). If `Y` is an algebraic
stack (`[AlgebraicStack Y]`), then `X` is an algebraic stack over `S`. -/
@[stacks 05UN] #check
  (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.source_isAlgebraicStack :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack Y] (f : X ⟶ Y)
      (hf : relativelyRepresentableByAlgebraicSpaces f), AlgebraicStack X)

end AlgebraicGeometry
