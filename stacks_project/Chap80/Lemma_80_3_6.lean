/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 80.3.6: let `S` be a scheme contained in `Sch_fppf`. Let
`F, G : (Over S)ᵒᵖ ⥤ Type u` be functors on `(Sch/S)_fppf`, and let
`a : F ⟶ G` be representable by algebraic spaces. If `G` is an algebraic space,
then so is `F`. -/
@[stacks 02YS] #check
  (AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpace.of_representableByAlgebraicSpaces :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
      [IsAlgebraicSpace G], representableByAlgebraicSpaces a → IsAlgebraicSpace F)

end AlgebraicGeometry.AlgebraicSpace
