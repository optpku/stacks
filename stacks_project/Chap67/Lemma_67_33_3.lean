/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ResidueFieldTrdeg
import StacksCheckRecall

/-!
# Comparison of residue-field transcendence degrees

A locally quasi-finite first arrow does not change the residue-field
transcendence degree over a locally finite type target.
-/

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 67.33.3: Let `S` be a scheme. Let `X ⟶ Y ⟶ Z` be morphisms of
algebraic spaces over `S`. Let `x` be a point of `X`, and write `y` and `z`
for the images `Points.map f x` and `Points.map (f ≫ g) x`. If `f` is locally
quasi-finite and `g` is locally of finite type, then the transcendence degree
of `x` over `z` equals the transcendence degree of `y` over `z`. -/
@[stacks 06RX] #check
  (AlgebraicGeometry.AlgebraicSpace.residueFieldTrdegAt.comp_eq_of_locallyQuasiFinite :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [LocallyQuasiFinite f] [LocallyOfFiniteType g] (x : Points X),
      residueFieldTrdegAt (f ≫ g) x = residueFieldTrdegAt g (Points.map f x))
