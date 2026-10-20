/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Property.Composition
import StacksCheckRecall

/-!
# Composition of transferred morphism properties of algebraic spaces

If a morphism property of algebraic spaces is as in Definition 80.4.1 and
stable under composition, then so is its transfer to morphisms of
presheaves representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 80.4.3: let `S` be a scheme. Let `P` be a property as in
Definition 80.4.1 (stable under base change and fppf local on the target),
and assume `P` is stable under composition. For maps `a : F ⟶ G` and
`b : G ⟶ H` of presheaves on `(Sch/S)_fppf`, if `a` and `b` are
representable by algebraic spaces and have `P`, then so does `a ≫ b`
(Stacks `b ∘ a`). -/
@[stacks 046G] #check
  (AlgebraicGeometry.AlgebraicSpace.relativeAlgebraicSpaces.isStableUnderComposition :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
      [P.IsStableUnderBaseChange] [P.IsLocalAtTarget (fppfPrecoverage S)]
      [P.IsStableUnderComposition],
      (relativeAlgebraicSpaces P).IsStableUnderComposition)

#check (AlgebraicGeometry.AlgebraicSpace.relativeAlgebraicSpaces.comp :
  ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget (fppfPrecoverage S)]
    [P.IsStableUnderComposition] {F G H : (Over S)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) (b : G ⟶ H),
    relativeAlgebraicSpaces P a → relativeAlgebraicSpaces P b →
      relativeAlgebraicSpaces P (a ≫ b))

end AlgebraicGeometry.AlgebraicSpace
