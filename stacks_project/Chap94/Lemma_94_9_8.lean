/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap94.Definition_94_12_1_Representable
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.TwoFibreProduct
import StacksCheckRecall

/-!
# Base change of a representable-by-spaces morphism along a space

If a 1-morphism of groupoid fibrations over `(Sch/S)_fppf` is representable by
algebraic spaces and the second leg is representable by an algebraic space, then
the 2-fibre product is representable by an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/- Lemma 94.9.8: let `S` be an object of `Sch_fppf`. Let `X`, `Y`, `Z` be
categories fibred in groupoids over `(Sch/S)_fppf`. If `f : X ⟶ Y` is a
1-morphism representable by algebraic spaces and `Z` is representable by an
algebraic space over `S`, then the 2-fibre product `TwoFibreProduct.apex g f`
is representable by an algebraic space. -/
@[stacks 0300] #check
  (AlgebraicGeometry.IsRepresentableByAlgebraicSpace.twoFibreProduct :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Z ⟶ Y),
    relativelyRepresentableByAlgebraicSpaces f → IsRepresentableByAlgebraicSpace Z →
    IsRepresentableByAlgebraicSpace
      (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f))

end AlgebraicGeometry
