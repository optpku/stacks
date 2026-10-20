/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.ClosedSubscheme
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

/- Lemma 31.31.1: A closed subscheme of a quasi-compact relative projective spectrum is the
relative projective spectrum of the quotient by the kernel of the canonical map to the
pushed-forward restricted twists. -/
@[stacks 0801] #check
  (AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation.existsClosedSubschemeQuotientPresentation :
    ∀ {S X Z : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S}
      (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf) [𝒜.IsCommutative]
      (hqc : 𝒜.IsQuasicoherent)
      (A σ : S.affineOpens → Type u)
      [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
      [∀ U, AddSubgroupClass (σ U) (A U)]
      (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
      [∀ U, GradedRing (sectionGrading U)]
      (P : ∀ U : S.affineOpens, AlgebraicGeometry.ProjTwistPresentation (sectionGrading U))
      (model : ∀ (U : S.affineOpens) (d : ℕ),
        (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃ sectionGrading U d)
      (presentation : AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation
        𝒜 A σ sectionGrading P model p)
      (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i]
      [AlgebraicGeometry.QuasiCompact p],
      Nonempty
        (AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation.CanonicalClosedSubschemeQuotient
          presentation i))
