/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.AffineBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Domination
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction

/-!
# Admissible blowup domination over a Noetherian local ring

A proper modification of a local affine base is dominated by a blowup
admissible over the complement of its closed point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AffineFormalAlgebraicSpace
open IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.completionAlong

/-- The open subspace of `specOver hA` complementary to the closed subset
defined by the maximal ideal of the local ring. -/
abbrev maximalIdealComplement {A : Type u} [CommRing A] [IsLocalRing A]
    {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) : OpenSubspace (specOver hA) :=
  OpenSubspace.fromOpens (zeroLocusPoints hA (IsLocalRing.maximalIdeal A)).compl

/-- A proper locally finite type morphism to the spectrum of a Noetherian local
ring that is an isomorphism away from its closed point is dominated by a blowup
admissible over the complement of that point. -/
@[stacks 0AE6]
theorem exists_isAdmissibleBlowup_dominating {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S)
    (Y : Source (specOver hA) (zeroLocusPoints hA (maximalIdeal A)))
    [Proper Y.obj.hom] :
    ∃ (S' : AlgebraicSpace S) (b : S' ⟶ specOver hA) (g : S' ⟶ Y.obj.left),
      AlgebraicGeometry.AlgebraicSpace.IsAdmissibleBlowup (maximalIdealComplement hA) b ∧
        g ≫ Y.obj.hom = b :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.completionAlong
