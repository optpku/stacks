/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent.Pullback
import StacksCheckRecall

universe u

open AlgebraicGeometry CategoryTheory

variable {S : Scheme.{u}} {B : AlgebraicSpace S}
variable {G H : GroupoidAlgebraicSpace B} (f : GroupoidAlgebraicSpace.Hom G H)

/- Lemma 78.12.3: a morphism `f : GroupoidAlgebraicSpace.Hom G H` of groupoids in algebraic
spaces over `B` induces the pullback functor `(F, α) ↦ (f^* F, f^* α)` from equivariant
quasi-coherent modules on `H` to equivariant quasi-coherent modules on `G`. -/
@[stacks 0442] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh.pullback f : H.QCoh ⥤ G.QCoh)
