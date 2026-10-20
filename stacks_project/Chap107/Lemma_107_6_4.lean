/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension.Cogroupoid
import StacksCheckRecall

/-!
# Dimension of the local ring via a presenting cogroupoid

A compatible versal complete-local cogroupoid presentation computes the
local-ring dimension at a finite-type field-valued point as `2 dim A - dim B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.AlgebraicStack (FieldValuedPoint)
open AlgebraicGeometry.GroupoidsOver.Predeformation
open FiberedCategoryOver.Groupoids
open CompleteLocalAlgCat
open GroupoidInFunctors
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 107.6.4. The local-ring dimension at a finite-type field-valued point
is twice the dimension of the object algebra minus the dimension of the arrow
algebra of a compatible versal cogroupoid presentation. -/
@[stacks 0DSB] #check
  (AlgebraicGeometry.AlgebraicStack.localRingDimAt_eq_cogroupoid :
    ∀ {S : Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    [IsLocallyNoetherian X] (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Algebra Λ x0.K]
    [Module.Finite Λ x0.K]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ x0.K)) ≫ openImmersion =
        x0.structureHom)
    (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor))
    [_root_.FormalObject.IsVersal ξ]
    (B : CompleteLocalAlgCat Λ x0.K) (s t : ξ.base ⟶ B) (c : B ⟶ pushout s t)
    (h : IsPredeformationCogroupoid x0 openImmersion h_factor ξ B s t c)
    (hx : IsFiniteTypePoint (Points.mk x0)),
    localRingDimAt (Points.mk x0) hx =
      dimensionDiff (ringKrullDim ξ.base.carrier + ringKrullDim ξ.base.carrier)
        (ringKrullDim B.carrier))

end AlgebraicGeometry.AlgebraicStack
