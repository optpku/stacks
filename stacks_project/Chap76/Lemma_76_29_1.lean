/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Fiber.GeometricallyReduced
import StacksCheckRecall

/-!
# Geometric reducedness of fibres of morphisms of algebraic spaces

At a point of `Points Y`, geometric reducedness of the scheme-theoretic fibre of a
morphism of algebraic spaces is independent of the field-valued representative, and
equivalent to reducedness of every such fibre.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.29.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Let `y` be a point of `Points Y`. The following are equivalent:
for some morphism `Spec (.of k) ⟶ Y` in the equivalence class of `y` the algebraic
space `fiberOverField f p` is geometrically reduced over `k`; for every such
morphism the fibre is geometrically reduced over `k`; and for every such morphism
the fibre is reduced. -/
@[stacks 0E07] #check (AlgebraicGeometry.AlgebraicSpace.geometricallyReducedFiber_tfae :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y),
    List.TFAE
      [∃ p : FieldValuedPoint Y, Points.mk p = y ∧ GeometricallyReduced (fiberOverField f p),
        ∀ p : FieldValuedPoint Y, Points.mk p = y → GeometricallyReduced (fiberOverField f p),
        ∀ p : FieldValuedPoint Y, Points.mk p = y → IsReduced (fiberOverField f p)])
