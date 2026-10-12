/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Data.PNat.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import stacks_project.Chap30.Lemma_30_28_1_AdicThickening
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints

/-!
# Algebraization of dimension ≤ 1 cartesian ladders of algebraic spaces

A cartesian successor ladder of algebraic spaces over the adic spectra of a
complete local Noetherian ring, with proper first stage of dimension at most
one, algebraizes to a projective morphism of schemes.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace AdicThickening

/-- The adic stage `S_n = Spec(A ⧸ m^n)` as an algebraic space over `Spec(A)`. -/
def specStage (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ+) :
    AlgebraicSpace (Spec (CommRingCat.of A)) :=
  ofOver (Over.mk (Scheme.AdicThickening.toAmbient (IsLocalRing.maximalIdeal A) n))

/-- `specStage A n` is the algebraic space associated to the scheme-theoretic
adic spectrum `Scheme.AdicThickening.spec (IsLocalRing.maximalIdeal A) n`. -/
theorem specStage_def (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ+) :
    specStage A n =
      ofOver (Over.mk (Scheme.AdicThickening.toAmbient (IsLocalRing.maximalIdeal A) n)) :=
  sorry

/-- The closed immersion `S_n ⟶ S_{n+1}` of successive adic stages, as a morphism
of algebraic spaces over `Spec(A)`. -/
def specStageTransition (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ+) :
    specStage A n ⟶ specStage A (n + 1) :=
  ofOverHomMk (Scheme.AdicThickening.specTransition (IsLocalRing.maximalIdeal A) n)
    (Scheme.AdicThickening.specTransition_comp_toAmbient (IsLocalRing.maximalIdeal A) n)

/-- `specStageTransition A n` is `ofOverHomMk` of `Scheme.AdicThickening.specTransition`. -/
theorem specStageTransition_def (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ+) :
    specStageTransition A n =
      ofOverHomMk (Scheme.AdicThickening.specTransition (IsLocalRing.maximalIdeal A) n)
        (Scheme.AdicThickening.specTransition_comp_toAmbient
          (IsLocalRing.maximalIdeal A) n) :=
  sorry

end AdicThickening

open AdicThickening

/-- Lemma 76.43.5: Let `(A, m, κ)` be a complete local Noetherian ring. Set
`S = Spec(A)` and `S_n = Spec(A ⧸ m^n)`. Given a commutative diagram of algebraic
spaces over `S` with cartesian successor squares `X n ⟶ X (n + 1)` over
`S_n ⟶ S_{n+1}`, if `toSpec 1` is proper and `dimension (X 1) ≤ 1`, then there
exists a projective morphism of schemes `π : W ⟶ S` together with identifications
`X n ≅ W ×_S S_n` compatible with the successor maps. -/
@[stacks 0E7R]
theorem exists_algebraizingProjective_of_dimension_le_one
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (X : ℕ+ → AlgebraicSpace (Spec (CommRingCat.of A)))
    (succ : ∀ n, X n ⟶ X (n + 1)) (toSpec : ∀ n, X n ⟶ specStage A n)
    (h_pb : ∀ n,
      IsPullback (succ n) (toSpec n) (toSpec (n + 1)) (specStageTransition A n))
    [Proper (toSpec 1)] (hdim : dimension (X 1) ≤ 1) :
    ∃ (W : Scheme.{u}) (π : W ⟶ Spec (CommRingCat.of A))
      (e : ∀ n, X n ⟶ ofOver (Over.mk π)),
      HProjective π ∧ (∀ n, e n = succ n ≫ e (n + 1)) ∧
        ∀ n, IsPullback (e n) (toSpec n) (toBase (ofOver (Over.mk π)))
          (toBase (specStage A n)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
