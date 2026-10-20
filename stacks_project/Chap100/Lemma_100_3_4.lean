/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.MorphismProperty
import StacksCheckRecall

/-!
# Testing representable morphisms of algebraic stacks on a stacky fppf covering

A property of morphisms of algebraic spaces that is fppf local on the target
and stable under base change may be tested on the 2-fibre-product projection
of one representable, surjective, flat, locally of finite presentation base
change of a morphism of algebraic stacks representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/- Lemma 100.3.4: Let `P` be a property of morphisms of algebraic spaces that
is fppf local on the target and stable under base change. Let `f : X ⟶ Y` be a
morphism of algebraic stacks representable by algebraic spaces. Let
`g : Z ⟶ Y` be a morphism of algebraic stacks which is representable by
algebraic spaces, surjective, flat, and locally of finite presentation. Set
`W = Z ×_Y X`. Then `f` has `P` if and only if the projection
`TwoFibreProduct.fst g f : W ⟶ Z` has `P`. -/
@[stacks 06TY]
#check (AlgebraicGeometry.Groupoids.Hom.has_iff_of_weak_covering :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f)
    (g : Z ⟶ Y) [Surjective g] [Flat g] [LocallyOfFinitePresentation g],
    has P f ↔ has P (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f))

end AlgebraicGeometry.Groupoids.Hom
