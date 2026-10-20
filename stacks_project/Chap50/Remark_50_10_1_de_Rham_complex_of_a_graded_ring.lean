/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.RingTheory.Kaehler.DeRham.Grading

universe u v

/- Remark 50.10.1 (de Rham complex of a graded ring) (1): the homogeneous pieces of
`Ω[A⁄R]` form an internal direct sum. -/
@[stacks 0FU9] #check
  (KaehlerDifferential.DeRham.Grading.onePiece_isInternal :
    ∀ {G : Type v} [DecidableEq G] [AddCommMonoid G]
      (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
      (𝒜 : G → Submodule R A) [GradedAlgebra 𝒜],
      DirectSum.IsInternal (KaehlerDifferential.DeRham.Grading.onePiece R A 𝒜))

/- Remark 50.10.1 (de Rham complex of a graded ring) (2): for every `p`, the homogeneous
pieces of `Ω^p_{A/R}` form an internal direct sum. -/
@[stacks 0FU9] #check
  (KaehlerDifferential.DeRham.Grading.piece_isInternal :
    ∀ {G : Type v} [DecidableEq G] [AddCommMonoid G]
      (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
      (𝒜 : G → Submodule R A) [GradedAlgebra 𝒜] (p : ℕ),
      DirectSum.IsInternal (KaehlerDifferential.DeRham.Grading.piece R A 𝒜 p))

/- Remark 50.10.1 (de Rham complex of a graded ring) (3): the de Rham differential preserves
the grading degree. -/
@[stacks 0FU9] #check
  (KaehlerDifferential.DeRham.Grading.d_mem :
    ∀ {G : Type v} [DecidableEq G] [AddCommMonoid G]
      (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
      (𝒜 : G → Submodule R A) [GradedAlgebra 𝒜]
      {p : ℕ} {g : G} {x : KaehlerDifferential.DeRham.term R A p},
      x ∈ KaehlerDifferential.DeRham.Grading.piece R A 𝒜 p g →
        KaehlerDifferential.DeRham.d R A p x ∈
          KaehlerDifferential.DeRham.Grading.piece R A 𝒜 (p + 1) g)

/- Remark 50.10.1 (de Rham complex of a graded ring) (4): wedge multiplication sends grading
degrees `g` and `h` to `g + h`. -/
@[stacks 0FU9] #check
  (KaehlerDifferential.DeRham.Grading.wedge_mem :
    ∀ {G : Type v} [DecidableEq G] [AddCommMonoid G]
      (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
      (𝒜 : G → Submodule R A) [GradedAlgebra 𝒜]
      {p q : ℕ} {g h : G}
      {x : KaehlerDifferential.DeRham.term R A p}
      {y : KaehlerDifferential.DeRham.term R A q},
      x ∈ KaehlerDifferential.DeRham.Grading.piece R A 𝒜 p g →
      y ∈ KaehlerDifferential.DeRham.Grading.piece R A 𝒜 q h →
      KaehlerDifferential.DeRham.formWedgeBilinear R A p q x y ∈
      KaehlerDifferential.DeRham.Grading.piece R A 𝒜 (p + q) (g + h))
