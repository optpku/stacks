/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictTransform.Flat
import StacksCheckRecall

/-!
# Lemma 71.18.4

Pointwise flatness over the center makes the strict transform of an algebraic
space (resp. a quasi-coherent module) coincide with the ambient base change
(resp. the pullback), via invertibility of the canonical closed immersion
(resp. quotient).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 71.18.4 (1): flatness over the center identifies the strict transform
with the ambient base change through its canonical inclusion. -/
@[stacks 0865] #check
  (AlgebraicGeometry.AlgebraicSpace.strictTransform_ι_isIso_of_flatAt_over_center :
    ∀ {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
      (Z : ClosedSubspace B) (b : B' ⟶ B) [IsBlowup b Z] (f : X ⟶ B)
      [QuasiCompact (strictTransformOpenComplement b (Z.inverseImageSubspace b) f).ι],
      (∀ x : Points X, Points.map f x ∈ Z.pointsSet → FlatAt f x) →
      IsIso (strictTransform b (Z.inverseImageSubspace b) f).ι)

/- Lemma 71.18.4 (2): relative flatness over the center identifies the module
strict transform with the pullback through its canonical quotient. -/
@[stacks 0865] #check
  (AlgebraicGeometry.AlgebraicSpace.strictTransformπ_isIso_of_flatOverAt_over_center :
    ∀ {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
      (Z : ClosedSubspace B) (b : B' ⟶ B) [IsBlowup b Z] (f : X ⟶ B)
      (F : X.Modules) [F.IsQuasicoherent],
      (∀ x : Points X, Points.map f x ∈ Z.pointsSet → Modules.flatOverAt F f x) →
      IsIso (strictTransformπ b (Z.inverseImageSubspace b) f F))
