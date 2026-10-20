/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissage.StandardShrinking

/-!
# Existence of standard shrinkings

This module provides standard shrinkings with prescribed control over the base,
model, or source open.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint.StandardShrinking

variable {S : Scheme.{u}} {X : Over S} {ℱ : X.left.Modules}
  [LocallyOfFiniteType X.hom] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] {x : X.left}

/-- Restriction to a prescribed basic-open neighbourhood of the base point gives a
standard shrinking whose four opens are the corresponding inverse images. -/
theorem existsOfBase (D : OneStepDevissageAtAmbientPoint X ℱ x) (S' : S.Opens)
    (a : Γ(S, ⊤)) (h_standard : S' = S.basicOpen a)
    (h_neighbourhood : X.hom x ∈ S') :
    ∃ W : D.StandardShrinking,
      W.base = S' ∧
        W.source = X.hom ⁻¹ᵁ S' ∧
        W.auxiliary = D.toOneStepDevissage.Z.hom ⁻¹ᵁ S' ∧
        W.model = D.toOneStepDevissage.Y.hom ⁻¹ᵁ S' := sorry

/-- Every basic-open neighbourhood of the distinguished model point is the model
open of a standard shrinking after restriction over its base. -/
theorem existsWithModel (D : OneStepDevissageAtAmbientPoint X ℱ x)
    (V : D.toOneStepDevissage.Y.left.Opens)
    (a : Γ(D.toOneStepDevissage.Y.left, ⊤))
    (h_standard : V = D.toOneStepDevissage.Y.left.basicOpen a)
    (h_neighbourhood : D.y ∈ V) :
    ∃ W : D.StandardShrinking,
      W.model = V ⊓ (D.toOneStepDevissage.Y.hom ⁻¹ᵁ W.base) := sorry

/-- Every open neighbourhood of the distinguished source point contains the source
open of a standard shrinking. -/
theorem existsSourceLE (D : OneStepDevissageAtAmbientPoint X ℱ x) (U : X.left.Opens)
    (h_neighbourhood : x ∈ U) :
    ∃ W : D.StandardShrinking, W.source ≤ U := sorry

end AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint.StandardShrinking
