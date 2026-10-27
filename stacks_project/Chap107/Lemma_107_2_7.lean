/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.VersalRing.SmoothLocus
import StacksCheckRecall

/-!
# Smoothness at a finite-type field-valued point

The image `s` is determined by `x0`. The residue compatibility in
`IsVersalRing.residue_iso` identifies it with the image of the closed point of `A`.
Thus the canonical map `Scheme.stalkClosedPointTo A.toS` has source `𝒪_{S,s}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open FiberedCategoryOver.Groupoids
open GroupoidsOver
open AlgebraicGeometry.GroupoidsOver.Predeformation
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 107.2.7: In Situation 107.2.1, for a finite-type field-valued point
and a versal ring, membership in the smooth locus, maximal-ideal-adic formal
smoothness of the canonical base-stalk map, and unobstructedness of the
predeformation category are equivalent. -/
@[stacks 0DZS] #check (AlgebraicGeometry.AlgebraicStack.mem_sourceLocus_tfae :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) [IsVersalRing x0 A],
    List.TFAE
      [Points.mk x0 ∈
          (Smooth.sourceLocus (baseProjection.{u + 1, u, u + 1} X)).pointsSet,
        (Scheme.stalkClosedPointTo A.toS).hom.formally_smooth_for_adic
          (maximalIdeal A.carrier),
        ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Algebra Λ x0.K]
          [Module.Finite Λ x0.K]
          (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
          [IsOpenImmersion openImmersion]
          (h_factor :
            Spec.map (CommRingCat.ofHom (algebraMap Λ x0.K)) ≫ openImmersion =
              x0.structureHom),
          Functor.IsUnobstructed
            (predeformationFunctor X openImmersion x0.structureHom h_factor
              x0.fiberObj)])

end AlgebraicGeometry.AlgebraicStack
