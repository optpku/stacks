/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property.Presheaf
import StacksCheckRecall

/-!
# Properties of representable maps of presheaves versus groupoid fibrations

A map of set-valued presheaves on `(Sch/S)_fppf` that is representable by
algebraic spaces has a morphism property `P` in the Bootstrap 80.4.1 sense if
and only if the associated 1-morphism of categories fibred in groupoids has `P`
in the Definition 94.10.1 sense.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/- Lemma 94.10.3: let `S` be a scheme in `Sch_fppf`. Let `a : F ⟶ G` be a map of
presheaves on `(Sch/S)_fppf` that is representable by algebraic spaces. Let `P`
be a property of morphisms of algebraic spaces that is stable under base change
and fppf local on the target, as in Definition 94.10.1. Then `a` has property `P`
in the sense of Bootstrap Definition 80.4.1 if and only if the corresponding
morphism `𝒮_F ⟶ 𝒮_G` of categories fibred in groupoids has property `P`. -/
@[stacks 045A] #check
  (AlgebraicGeometry.Groupoids.Hom.has_iff_ofPresheaf :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {a : F ⟶ G} (ha : AlgebraicSpace.representableByAlgebraicSpaces a),
    ha.has P ↔
      AlgebraicGeometry.Groupoids.Hom.has P
        ((Sets.toGroupoids (Over S)).map ((Sets.ofPresheaf (Over S)).map a)))

end AlgebraicGeometry.Groupoids.Hom
