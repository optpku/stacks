/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Morphisms
import StacksCheckRecall

/-!
# Morphisms of algebraic-space fibrations

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` is
representable by algebraic spaces whenever both source and target are.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/- Lemma 94.9.4: let `S` be an object of `Sch_fppf`. Let `f : X ⟶ Y` be a
1-morphism of categories fibred in groupoids over `S`. If `X` and `Y` are
representable by algebraic spaces over `S`, then `f` is representable by
algebraic spaces. -/
@[stacks 02ZZ] #check
  (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.of_isRepresentableByAlgebraicSpace :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
      (hX : IsRepresentableByAlgebraicSpace X)
      (hY : IsRepresentableByAlgebraicSpace Y),
      relativelyRepresentableByAlgebraicSpaces f)

/- The 1-morphism of groupoid fibrations associated to a morphism of algebraic
spaces over `S` is representable by algebraic spaces. -/
#check (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.of_toGroupoids_map :
    ∀ {S : Scheme.{u}} {F G : AlgebraicSpace S} (φ : F ⟶ G),
      relativelyRepresentableByAlgebraicSpaces (AlgebraicSpace.toGroupoids.map φ))

end AlgebraicGeometry
