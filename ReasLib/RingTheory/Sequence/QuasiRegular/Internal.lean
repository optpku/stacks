module

public import ReasLib.RingTheory.Sequence.QuasiRegular.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Internal associated-graded model for finite sequences

This leaf owns the internal quotient presentation
`I^n M / I (I^n M)` and its canonical comparison with
`Ideal.AssociatedGraded.piece I M n`.  The standard associated-graded object remains the data owner;
the internal presentation is a thin, named bridge for constructions that need stage subtypes.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

universe u v

namespace RingTheory.Sequence.QuasiRegular

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The stage quotient `I^n M / I (I^n M)` for the internal associated-graded presentation.

The quotient is an abbreviation, so it introduces no second carrier or module instance.  The
canonical `Ideal.AssociatedGraded.piece` remains the preferred public target for reusable APIs.
-/
@[stacks 061P "internal associated-graded stage quotient"]
abbrev internalPiece (rs : List R) (n : ℕ) : Type v :=
  Ideal.AssociatedGraded.stage (Ideal.ofList rs) M n ⧸
    ((Ideal.ofList rs) • ⊤ :
      Submodule R (Ideal.AssociatedGraded.stage (Ideal.ofList rs) M n))

/-- The direct sum of the internal stage quotients.

This is a compatibility presentation only; maps intended for broad reuse should target
`Ideal.AssociatedGraded.gradedModule` and use `internalAddEquiv` when a construction needs this
presentation.
-/
@[stacks 061P "internal associated-graded direct sum"]
abbrev internal (rs : List R) : Type v :=
  DirectSum ℕ (internalPiece (M := M) rs)

/-- The canonical linear equivalence from an internal stage quotient to the standard
associated-graded piece. -/
@[stacks 061P "internal piece comparison equivalence"]
noncomputable abbrev internalPieceEquiv (rs : List R) (n : ℕ) :
    internalPiece (M := M) rs n ≃ₗ[R]
      Ideal.AssociatedGraded.piece (Ideal.ofList rs) M n :=
  Ideal.AssociatedGraded.internalPieceEquiv (Ideal.ofList rs) M n

/-- The direct-sum additive equivalence induced by `internalPieceEquiv`.

This named comparison avoids rebuilding a family of casts and preserves a single route back to the
canonical associated-graded direct sum.
-/
@[stacks 061P "internal associated-graded comparison equivalence"]
noncomputable abbrev internalAddEquiv (rs : List R) :
    Ideal.AssociatedGraded.gradedModule (Ideal.ofList rs) M ≃+
      internal (M := M) rs :=
  DirectSum.congrAddEquiv fun n ↦
    (internalPieceEquiv (M := M) rs n).symm.toAddEquiv

/-- The polynomial action on the internal presentation, transported from the
canonical associated-graded module. -/
@[stacks 061P "polynomial action on the internal associated-graded model"]
noncomputable def internalPolynomialSmul (rs : List R)
    (p : MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
    (x : internal (M := M) rs) : internal (M := M) rs :=
  internalAddEquiv (M := M) rs
    (p • (internalAddEquiv (M := M) rs).symm x)

/-- The polynomial module structure on the internal direct-sum presentation.

The structure is transported from the canonical associated-graded module through
`internalAddEquiv`; it is a named global instance so downstream users do not rebuild an
incompatible polynomial action or install a local instance. -/
@[stacks 061P "polynomial module on the internal associated-graded model"]
noncomputable instance internalModule (rs : List R) :
    Module (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
      (internal (M := M) rs) :=
  (internalAddEquiv (M := M) rs).symm.module
    (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))

/-- The inferred polynomial scalar action on the internal presentation is the
explicit transported action `internalPolynomialSmul`. -/
@[stacks 061P "internal polynomial scalar action formula"]
theorem internal_smul_eq (rs : List R)
    (p : MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
    (x : internal (M := M) rs) :
    p • x = internalPolynomialSmul (M := M) rs p x := sorry

/-- The additive internal comparison is polynomial-linear for the transported
module structure. -/
@[simp, stacks 061P "polynomial linearity of the internal additive comparison"]
theorem internalAddEquiv_map_smul (rs : List R)
    (p : MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
    (x : Ideal.AssociatedGraded.gradedModule (Ideal.ofList rs) M) :
    internalAddEquiv (M := M) rs (p • x) =
      p • internalAddEquiv (M := M) rs x := sorry

/-- Coefficient scalars act through polynomial scalars on the internal
associated-graded presentation. -/
@[stacks 061P "coefficient-polynomial scalar tower on the internal model"]
theorem internalScalarTower (rs : List R) :
    IsScalarTower (R ⧸ Ideal.ofList rs)
      (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
      (internal (M := M) rs) := sorry

/-- The canonical coefficient-to-polynomial scalar tower on the internal model. -/
@[stacks 061P "internal coefficient-polynomial scalar tower instance"]
noncomputable instance internalScalarTowerInstance (rs : List R) :
    IsScalarTower (R ⧸ Ideal.ofList rs)
      (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
      (internal (M := M) rs) :=
  internalScalarTower (M := M) rs

/-- The polynomial-linear equivalence between the canonical and internal
associated-graded presentations. -/
@[stacks 061P "linear internal associated-graded comparison"]
noncomputable def internalLinearEquiv (rs : List R) :
    Ideal.AssociatedGraded.gradedModule (Ideal.ofList rs) M ≃ₗ[
      MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)]
      internal (M := M) rs :=
  ((internalAddEquiv (M := M) rs).symm.linearEquiv
    (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))).symm

/-- The linear internal comparison has the same underlying function as the
canonical additive comparison. -/
@[simp, stacks 061P "linear internal comparison computation"]
theorem internalLinearEquiv_apply (rs : List R)
    (x : Ideal.AssociatedGraded.gradedModule (Ideal.ofList rs) M) :
    internalLinearEquiv (M := M) rs x = internalAddEquiv (M := M) rs x := sorry

/-- The inverse linear internal comparison has the same underlying function as the
inverse additive comparison. -/
@[simp, stacks 061P "inverse linear internal comparison computation"]
theorem internalLinearEquiv_symm_apply (rs : List R) (x : internal (M := M) rs) :
    (internalLinearEquiv (M := M) rs).symm x =
      (internalAddEquiv (M := M) rs).symm x := sorry

end RingTheory.Sequence.QuasiRegular

end
