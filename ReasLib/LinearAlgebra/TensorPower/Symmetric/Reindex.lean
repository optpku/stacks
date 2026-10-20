module

public import Mathlib.LinearAlgebra.TensorPower.Symmetric

@[expose] public section

open scoped TensorProduct

/-!
# Reindexing symmetric tensor powers

Symmetric tensor powers are functorial in equivalences of their indexing types. This file
packages the quotient-level reindexing map, rather than requiring consumers to descend
`PiTensorProduct.reindex` through the permutation relation themselves.
-/

namespace SymmetricPower

universe u v

section

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {ι ι' ι'' : Type u}

namespace Internal

/-- Reindexing tensor powers preserves the symmetric-power permutation relation. -/
theorem reindexRel (e : ι ≃ ι') {x y : ⨂[R] (_ : ι), M}
    (h : addConGen (Rel R ι M) x y) :
    addConGen (Rel R ι' M)
      (PiTensorProduct.reindex R (fun _ ↦ M) e x)
      (PiTensorProduct.reindex R (fun _ ↦ M) e y) := sorry

end Internal

/-- The linear equivalence on symmetric tensor powers induced by an equivalence of index types. -/
noncomputable def reindex (e : ι ≃ ι') :
    Sym[R] ι M ≃ₗ[R] Sym[R] ι' M :=
  LinearEquiv.ofLinear
    { __ :=
        AddCon.lift _
          ((SymmetricPower.mk R ι' M).toAddMonoidHom.comp
            (PiTensorProduct.reindex R (fun _ ↦ M) e).toLinearMap.toAddMonoidHom)
          (fun x y h ↦ Quotient.sound (Internal.reindexRel e h))
      map_smul' r q := by
        refine AddCon.induction_on q ?_
        intro x
        change SymmetricPower.mk R ι' M
            (PiTensorProduct.reindex R (fun _ ↦ M) e (r • x)) =
          SymmetricPower.smul' ι' M r
            (SymmetricPower.mk R ι' M (PiTensorProduct.reindex R (fun _ ↦ M) e x))
        rw [show SymmetricPower.smul' ι' M r
            (SymmetricPower.mk R ι' M (PiTensorProduct.reindex R (fun _ ↦ M) e x)) =
              SymmetricPower.mk R ι' M
                (r • PiTensorProduct.reindex R (fun _ ↦ M) e x) by
                  rfl]
        simp }
    { __ :=
        AddCon.lift _
          ((SymmetricPower.mk R ι M).toAddMonoidHom.comp
            (PiTensorProduct.reindex R (fun _ ↦ M) e.symm).toLinearMap.toAddMonoidHom)
          (fun x y h ↦ Quotient.sound (Internal.reindexRel e.symm h))
      map_smul' r q := by
        refine AddCon.induction_on q ?_
        intro x
        change SymmetricPower.mk R ι M
            (PiTensorProduct.reindex R (fun _ ↦ M) e.symm (r • x)) =
          SymmetricPower.smul' ι M r
            (SymmetricPower.mk R ι M (PiTensorProduct.reindex R (fun _ ↦ M) e.symm x))
        rw [show SymmetricPower.smul' ι M r
            (SymmetricPower.mk R ι M (PiTensorProduct.reindex R (fun _ ↦ M) e.symm x)) =
              SymmetricPower.mk R ι M
                (r • PiTensorProduct.reindex R (fun _ ↦ M) e.symm x) by
                  rfl]
        simp }
    (by
      ext q
      refine AddCon.induction_on q ?_
      intro x
      change SymmetricPower.mk R ι' M
          (PiTensorProduct.reindex R (fun _ ↦ M) e
            (PiTensorProduct.reindex R (fun _ ↦ M) e.symm x)) =
          SymmetricPower.mk R ι' M x
      simpa using
        congrArg (SymmetricPower.mk R ι' M) (PiTensorProduct.reindex_reindex e.symm e x))
    (by
      ext q
      refine AddCon.induction_on q ?_
      intro x
      change SymmetricPower.mk R ι M
          (PiTensorProduct.reindex R (fun _ ↦ M) e.symm
            (PiTensorProduct.reindex R (fun _ ↦ M) e x)) =
          SymmetricPower.mk R ι M x
      simpa using
        congrArg (SymmetricPower.mk R ι M) (PiTensorProduct.reindex_reindex e e.symm x))

/-- `SymmetricPower.reindex` on a quotient representative. -/
@[simp] theorem reindex_mk (e : ι ≃ ι') (x : ⨂[R] (_ : ι), M) :
    reindex e (SymmetricPower.mk R ι M x) =
      SymmetricPower.mk R ι' M (PiTensorProduct.reindex R (fun _ ↦ M) e x) := sorry

/-- `SymmetricPower.reindex` on a pure symmetric tensor. -/
@[simp] theorem reindex_tprod (e : ι ≃ ι') (m : ι → M) :
    reindex e (SymmetricPower.tprod R m) = SymmetricPower.tprod R (m ∘ e.symm) := sorry

/-- Reindexing along the identity equivalence is the identity linear equivalence. -/
@[simp] theorem reindex_refl :
    reindex (Equiv.refl ι) = LinearEquiv.refl R (Sym[R] ι M) := sorry

/-- The inverse of a symmetric-power reindexing map is induced by the inverse index equivalence. -/
@[simp] theorem reindex_symm (e : ι ≃ ι') :
    (reindex (R := R) (M := M) e).symm = reindex (R := R) (M := M) e.symm := sorry

/-- Symmetric-power reindexing maps compose with the underlying index equivalences. -/
@[simp] theorem reindex_trans (e : ι ≃ ι') (e' : ι' ≃ ι'') :
    (reindex (R := R) (M := M) e).trans (reindex (R := R) (M := M) e') =
      reindex (R := R) (M := M) (e.trans e') := sorry

end

end SymmetricPower
