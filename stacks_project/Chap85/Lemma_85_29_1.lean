/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap85.Lemma_85_29_1_Nerve
import StacksCheckRecall

/-!
# Lemma 85.29.1

A groupoid scheme over `S` determines a 2-coskeletal simplicial scheme over `S`, with the
stated low-degree identities and with degree `n` the n-fold fibre product of `R` over `(s, t)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Simplicial

universe u

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/- Lemma 85.29.1 (1): a groupoid scheme over `S` determines a 2-coskeletal simplicial scheme `X`. -/
@[stacks 07TN]
#check GroupoidScheme.simplicialScheme

/- Lemma 85.29.1 (2): `X _⦋0⦌` is the object scheme `U`. -/
@[stacks 07TN]
#check GroupoidScheme.degreeZero.iso

/- Lemma 85.29.1 (3): `X _⦋1⦌` is the arrow scheme `R`. -/
@[stacks 07TN]
#check GroupoidScheme.degreeOne.iso

/- Lemma 85.29.1 (4): `X _⦋2⦌` is the fibre product `R ×_{s,U,t} R`. -/
@[stacks 07TN]
#check GroupoidScheme.degreeTwo.iso

/-- Lemma 85.29.1 (5): the degeneracy `s_0^0` is the identity-arrow map `e`. -/
@[stacks 07TN]
theorem simplicialScheme_degeneracy_zero :
    (GroupoidScheme.degreeZero.iso G).inv ≫ (G.simplicialScheme).σ 0 ≫
        (GroupoidScheme.degreeOne.iso G).hom =
      G.e.left :=
  sorry

/-- Lemma 85.29.1 (6): the face `d^1_0` is the source map `s`. -/
@[stacks 07TN]
theorem simplicialScheme_face_one_zero :
    (GroupoidScheme.degreeOne.iso G).inv ≫ (G.simplicialScheme).δ 0 ≫
        (GroupoidScheme.degreeZero.iso G).hom =
      G.s.left :=
  sorry

/-- Lemma 85.29.1 (7): the face `d^1_1` is the target map `t`. -/
@[stacks 07TN]
theorem simplicialScheme_face_one_one :
    (GroupoidScheme.degreeOne.iso G).inv ≫ (G.simplicialScheme).δ 1 ≫
        (GroupoidScheme.degreeZero.iso G).hom =
      G.t.left :=
  sorry

/-- Lemma 85.29.1 (8): the degeneracy `s_0^1` is `(e ∘ t, 1)`. -/
@[stacks 07TN]
theorem simplicialScheme_degeneracy_one_zero :
    (GroupoidScheme.degreeOne.iso G).inv ≫ (G.simplicialScheme).σ 0 ≫
        (GroupoidScheme.degreeTwo.iso G).hom =
      (GroupoidScheme.degeneracy_one_zero G).left :=
  sorry

/-- Lemma 85.29.1 (9): the degeneracy `s_1^1` is `(1, e ∘ s)`, the identity-at-source lift. -/
@[stacks 07TN]
theorem simplicialScheme_degeneracy_one_one :
    (GroupoidScheme.degreeOne.iso G).inv ≫ (G.simplicialScheme).σ 1 ≫
        (GroupoidScheme.degreeTwo.iso G).hom =
      (GroupoidScheme.degeneracy_one_one G).left :=
  sorry

/-- Lemma 85.29.1 (10): the face `d^2_0` is the earlier-arrow projection `pr_1`. -/
@[stacks 07TN]
theorem simplicialScheme_face_two_zero :
    (GroupoidScheme.degreeTwo.iso G).inv ≫ (G.simplicialScheme).δ 0 ≫
        (GroupoidScheme.degreeOne.iso G).hom =
      (pullback.snd G.s G.t).left :=
  sorry

/-- Lemma 85.29.1 (11): the face `d^2_1` is the composition map `c`. -/
@[stacks 07TN]
theorem simplicialScheme_face_two_one :
    (GroupoidScheme.degreeTwo.iso G).inv ≫ (G.simplicialScheme).δ 1 ≫
        (GroupoidScheme.degreeOne.iso G).hom =
      G.c.left :=
  sorry

/-- Lemma 85.29.1 (12): the face `d^2_2` is the later-arrow projection `pr_0`. -/
@[stacks 07TN]
theorem simplicialScheme_face_two_two :
    (GroupoidScheme.degreeTwo.iso G).inv ≫ (G.simplicialScheme).δ 2 ≫
        (GroupoidScheme.degreeOne.iso G).hom =
      (pullback.fst G.s G.t).left :=
  sorry

/- Lemma 85.29.1 (13): `X = cosk₂ sk₂ X`. -/
@[stacks 07TN]
#check GroupoidScheme.simplicialScheme.instIsCoskeletal

/- Lemma 85.29.1 (14): the n-fold fibre product of `R` over `(s, t)`. -/
@[stacks 07TN]
#check GroupoidScheme.composable

/-- Lemma 85.29.1 (15): the comparison identifying `X_n` with the n-fold fibre product is an
isomorphism. -/
@[stacks 07TN]
theorem simplicialScheme_composableComparison_isIso (n : ℕ) :
    IsIso (GroupoidScheme.composableComparison G n) :=
  sorry

/-- Lemma 85.29.1 (16): adjacent later-first projections are composable over `(s, t)`. -/
@[stacks 07TN]
theorem simplicialScheme_composableπ_adjacent (n : ℕ) (i : Fin n) :
    GroupoidScheme.composableπ G (n + 1) i.castSucc ≫ G.s =
      GroupoidScheme.composableπ G (n + 1) i.succ ≫ G.t :=
  sorry

/-- Lemma 85.29.1 (17): an interior face copies factors before the composed slot. -/
@[stacks 07TN]
theorem simplicialScheme_face_interior_π_lt (n : ℕ) (j : Fin (n + 2)) (k : Fin n)
    (hj0 : 0 < (j : ℕ)) (hjn : (j : ℕ) < n + 1) (hk : (k : ℕ) < (j : ℕ) - 1) :
    GroupoidScheme.composable.face G n j ≫ GroupoidScheme.composableπ G n k =
      GroupoidScheme.composableπ G (n + 1) k.castSucc :=
  sorry

/-- Lemma 85.29.1 (18): an interior face composes the two adjacent factors. -/
@[stacks 07TN]
theorem simplicialScheme_face_interior_π_eq (n : ℕ) (j : Fin (n + 2)) (k : Fin n)
    (hj0 : 0 < (j : ℕ)) (hjn : (j : ℕ) < n + 1) (hk : (k : ℕ) = (j : ℕ) - 1) :
    GroupoidScheme.composable.face G n j ≫ GroupoidScheme.composableπ G n k =
      G.compose (GroupoidScheme.composableπ G (n + 1) k.castSucc)
        (GroupoidScheme.composableπ G (n + 1) k.succ)
        (simplicialScheme_composableπ_adjacent G n k) :=
  sorry

/-- Lemma 85.29.1 (19): an interior face copies factors after the composed slot. -/
@[stacks 07TN]
theorem simplicialScheme_face_interior_π_gt (n : ℕ) (j : Fin (n + 2)) (k : Fin n)
    (hj0 : 0 < (j : ℕ)) (hjn : (j : ℕ) < n + 1) (hk : (j : ℕ) - 1 < (k : ℕ)) :
    GroupoidScheme.composable.face G n j ≫ GroupoidScheme.composableπ G n k =
      GroupoidScheme.composableπ G (n + 1) k.succ :=
  sorry

/-- Lemma 85.29.1 (20): the zeroth face drops the later-most factor. -/
@[stacks 07TN]
theorem simplicialScheme_face_zero_π (n : ℕ) (i : Fin n) :
    GroupoidScheme.composable.face G n 0 ≫ GroupoidScheme.composableπ G n i =
      GroupoidScheme.composableπ G (n + 1) i.succ :=
  sorry

/-- Lemma 85.29.1 (21): the last face drops the earlier-most factor. -/
@[stacks 07TN]
theorem simplicialScheme_face_last_π (n : ℕ) (i : Fin n) :
    GroupoidScheme.composable.face G n (Fin.last (n + 1)) ≫
        GroupoidScheme.composableπ G n i =
      GroupoidScheme.composableπ G (n + 1) i.castSucc :=
  sorry

/-- Lemma 85.29.1 (22): face operators on the n-fold fibre product match `X.δ`. -/
@[stacks 07TN]
theorem simplicialScheme_composableComparison_face (n : ℕ) (i : Fin (n + 2)) :
    (GroupoidScheme.composable.face G n i).left ≫
        GroupoidScheme.composableComparison G n =
      GroupoidScheme.composableComparison G (n + 1) ≫ (G.simplicialScheme).δ i :=
  sorry
