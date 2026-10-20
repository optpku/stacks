/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuasiCompact
import StacksCheckRecall

/-!
# Representable quasi-compact morphisms of algebraic spaces

A representable morphism of algebraic spaces is quasi-compact in the
sense of Section 67.3 if and only if every fibre product against a
quasi-compact algebraic space is quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.8.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a representable
morphism of algebraic spaces over `S`. Then `f` is quasi-compact in the
sense of Section 67.3 if and only if for every quasi-compact algebraic space
`Z` and any morphism `Z ⟶ Y` the algebraic space `Z ×_Y X` is quasi-compact. -/
@[stacks 03HD] #check
  (AlgebraicGeometry.AlgebraicSpace.quasiCompact_presheaf_iff_quasiCompact :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y},
      yoneda.relativelyRepresentable f →
        ((over (@AlgebraicGeometry.QuasiCompact : MorphismProperty Scheme.{u})).presheaf f ↔
          QuasiCompact f))

#check
  (AlgebraicGeometry.AlgebraicSpace.quasiCompact_of_presheaf :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y},
      yoneda.relativelyRepresentable f →
        (over (@AlgebraicGeometry.QuasiCompact : MorphismProperty Scheme.{u})).presheaf f →
          QuasiCompact f)

#check
  (AlgebraicGeometry.AlgebraicSpace.quasiCompact_presheaf_of_quasiCompact :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y},
      yoneda.relativelyRepresentable f → QuasiCompact f →
        (over (@AlgebraicGeometry.QuasiCompact : MorphismProperty Scheme.{u})).presheaf f)

#check
  (AlgebraicGeometry.AlgebraicSpace.quasiCompact_presheaf_iff_isQuasiCompact_of_isPullback :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y},
      yoneda.relativelyRepresentable f →
        ((over (@AlgebraicGeometry.QuasiCompact : MorphismProperty Scheme.{u})).presheaf f ↔
          ∀ {Z P : AlgebraicSpace S} {g : Z ⟶ Y} {pZ : P ⟶ Z} {pX : P ⟶ X}
            [IsQuasiCompact Z], IsPullback pZ pX g f → IsQuasiCompact P))

end AlgebraicGeometry.AlgebraicSpace
