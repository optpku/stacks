/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Degree.TwistComparison

open AlgebraicGeometry CategoryTheory Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

/- Lemma 27.16.8: an associated morphism to relative projective spectrum determines a unique
graded-algebra isomorphism from the pulled-back degree-`d` twists to the integral tensor powers
of the quadruple's invertible module, compatible with the universal graded map. -/
@[stacks 01O1] #check
  (AlgebraicGeometry.RelativeProjDegreeQuadruple.existsUnique_twistComparison_of_isAssociatedMorphism :
    ∀ {S : Scheme.{u}}
      (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf) [𝒜.IsCommutative]
      (d : ℕ) (hd : 1 ≤ d) [F : RelativeProjFunctor S 𝒜]
      (associatedToQuadruples :
        (F.degreeFunctor ⟨d, hd⟩).IsAssociatedToQuadruples)
      {A σ : S.affineOpens → Type u}
      [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
      [∀ U, AddSubgroupClass (σ U) (A U)]
      (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
      [∀ U, GradedRing (sectionGrading U)]
      (P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U))
      (model : ∀ (U : S.affineOpens) (n : ℕ),
        (𝒜 (Int.ofNat n)).val.obj (op (U : S.Opens)) ≃ sectionGrading U n)
      {X : Scheme.{u}} (π : X ⟶ S)
      (representedPoint : F.toFunctor.obj (op X))
      (representedPoint_isUniversal : F.toFunctor.IsRepresentedBy representedPoint)
      (presentation : AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation
        𝒜 A σ sectionGrading P model π)
      {T : Scheme.{u}} (q : RelativeProjDegreeQuadruple 𝒜 d T) (r : T ⟶ X)
      (h_assoc : AlgebraicGeometry.RelativeProjDegreeQuadruple.IsAssociatedMorphism
        hd associatedToQuadruples π representedPoint q r),
      ∃! θ : AlgebraicGeometry.RelativeProjDegreeQuadruple.TwistComparison presentation r q,
        AlgebraicGeometry.RelativeProjDegreeQuadruple.IsCompatibleTwistComparison
          presentation r q θ)
