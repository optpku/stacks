/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Groupoids.Hom
open scoped Bicategory

universe u

/- Lemma 94.10.6: let `S` be a scheme in `Sch_fppf`. Let `X`, `Y`, `Z` be
categories fibred in groupoids over `(Sch/S)_fppf`. Let `P` be a property of
morphisms of algebraic spaces as in Definition 94.10.1. Let `f : X ⟶ Y` be a
1-morphism representable by algebraic spaces, and let `g : Z ⟶ Y` be any
1-morphism. In the 2-fibre-product square of `(g, f)`, the base change is
`f' := TwoFibreProduct.fst g f : Z ×_Y X ⟶ Z` and the other projection is
`g' := TwoFibreProduct.snd g f`. If `f` has `P`, then `f'` has `P`.
Representability of `f'` is `relativelyRepresentableByAlgebraicSpaces.pullback_fst`
(Lemma 94.9.7). -/
@[stacks 045C]
#check (AlgebraicGeometry.Groupoids.Hom.has.pullback_fst :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    (f : X ⟶ Y) (g : Z ⟶ Y) (hf : relativelyRepresentableByAlgebraicSpaces f)
    (hP : has P f),
    has P (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f))
