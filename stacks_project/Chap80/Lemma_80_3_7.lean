/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 80.3.7: let `S` be a scheme. Let `a : F ⟶ G` be a morphism of
presheaves on `(Sch/S)_fppf` that is representable by algebraic spaces. If `X`
is an algebraic space over `S` and `f : X ⟶ G` is a map of presheaves, then the
fibre product `X ×_G F`, given by `pullback f a`, is an algebraic space. -/
@[stacks 03XY] #check
  (AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpace.pullback :
    ∀ {S : Scheme.{u}} {F G X : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G),
      representableByAlgebraicSpaces a → ∀ [IsAlgebraicSpace X] (f : X ⟶ G),
        IsAlgebraicSpace (pullback f a))

end AlgebraicGeometry.AlgebraicSpace
