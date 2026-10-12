/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Limits

/-!
# Countable affine-open covers

This file provides a countable reindexing of a finite affine-open cover of a scheme.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- A finite family of affine opens can be padded to an `ℕ`-indexed affine cover. -/
lemma natAffineFamilyOfFiniteCover {X : Scheme.{u}} {U : X.Opens} (s : Set X.Opens)
    (hs : s.Finite) (hsAffine : s ⊆ X.affineOpens) (hcover : sSup s = U) :
    ∃ V : ℕ → X.Opens, (∀ n, IsAffineOpen (V n)) ∧ iSup V = U := by
  classical
  by_cases hsEmpty : s = ∅
  · subst hsEmpty
    refine ⟨fun _ ↦ ⊥, fun _ ↦ isAffineOpen_bot X, ?_⟩
    -- An empty finite cover forces the target open to be bottom.
    simpa using hcover
  ·
    -- Local instance justification (proof-local temporary data): the proof-derived `Fintype` is scoped only to reindex the finite cover via `Fintype.equivFin`.
    letI : Fintype s := hs.fintype
    have hsSubtypeNonempty : Nonempty s := by
      rcases Set.nonempty_iff_ne_empty.mpr hsEmpty with ⟨W, hW⟩
      exact ⟨⟨W, hW⟩⟩
    let q : ℕ → s := fun n ↦
      (Fintype.equivFin s).symm
        ⟨n % Fintype.card s,
          Nat.mod_lt _ (Fintype.card_pos_iff.mpr hsSubtypeNonempty)⟩
    let V : ℕ → X.Opens := fun n ↦ (q n).1
    refine ⟨V, ?_, ?_⟩
    · intro n
      -- Every term of the padded family comes from the original affine family.
      exact hsAffine (q n).2
    · have hq : Function.Surjective q := by
        intro W
        refine ⟨(Fintype.equivFin s W).1, ?_⟩
        -- The first `card s` indices recover the original finite family exactly.
        have hfin :
            ⟨(Fintype.equivFin s W).1 % Fintype.card s,
              Nat.mod_lt _ (Fintype.card_pos_iff.mpr hsSubtypeNonempty)⟩ =
              Fintype.equivFin s W := by
          apply Fin.ext
          simpa using Nat.mod_eq_of_lt (Fintype.equivFin s W).2
        simpa [q] using congrArg (Fintype.equivFin s).symm hfin
      -- Surjectivity replaces the padded `ℕ`-indexed supremum by the finite supremum.
      calc
        iSup V = ⨆ W : s, ((W : s) : X.Opens) := by
          simpa [V] using hq.iSup_comp (fun W : s ↦ ((W : s) : X.Opens))
        _ = sSup s := by
          rw [← sSup_eq_iSup']
        _ = U := hcover

end AlgebraicGeometry.Scheme
