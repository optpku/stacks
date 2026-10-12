/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.PurelyInseparable.Lift

@[expose] public section

/-!
# Realized Finite Purely Inseparable Lifts

This leaf refines a finite purely inseparable lift by retaining the canonical
reduced tensor-product presentation of its top field.  One realization is a
single witness for the separability, compositum, and reduced-base-change
conclusions used throughout field theory.
-/

open scoped TensorProduct

universe u v w x

namespace FieldExtension.PurelyInseparable.Lift

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
variable {k' : Type w} [Field k'] [Algebra k k']
variable {K' : Type x} [Field K'] [Algebra k K'] [Algebra K K'] [Algebra k' K']
variable [IsScalarTower k K K'] [IsScalarTower k k' K']

/-- The canonical `k'`-algebra map from the scalar-base-change tensor product
to the top field of a lift. -/
def tensorProductMap : k' ⊗[k] K →ₐ[k'] K' :=
  Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId k' K')
    (IsScalarTower.toAlgHom k K K')

/-- Lemma 10.45.3, tag `030R`: a finite purely inseparable lift whose top
field is simultaneously the compositum of the two lower fields and the
reduced scalar-base-change tensor product. -/
@[stacks 030R]
structure Realization : Prop extends Lift k K k' K' where
  /-- The canonical tensor map has precisely the nilradical as kernel. -/
  ker_eq_nilradical :
    RingHom.ker (tensorProductMap (k := k) (K := K) (k' := k') (K' := K')).toRingHom =
      nilradical (k' ⊗[k] K)
  /-- The canonical tensor map is surjective. -/
  surjective : Function.Surjective
    (tensorProductMap (k := k) (K := K) (k' := k') (K' := K'))

namespace Realization

/-- The defining lift and reduced tensor-presentation conditions of a
realization. -/
theorem spec (h : Realization (k := k) (K := K) (k' := k') (K' := K')) :
    Lift k K k' K' ∧
      RingHom.ker (tensorProductMap (k := k) (K := K) (k' := k') (K' := K')).toRingHom =
        nilradical (k' ⊗[k] K) ∧
        Function.Surjective (tensorProductMap (k := k) (K := K) (k' := k') (K' := K')) := sorry

/-- The images of the lifted base and source fields generate the top field of
a realization. -/
theorem fieldRange_sup_eq_top
    (h : Realization (k := k) (K := K) (k' := k') (K' := K')) :
    (IsScalarTower.toAlgHom k k' K').fieldRange ⊔
      (IsScalarTower.toAlgHom k K K').fieldRange = ⊤ := sorry

/-- The canonical algebra equivalence from the reduced base-change tensor
product to the top field of a realization. -/
noncomputable def reducedTensorAlgEquiv
    (h : Realization (k := k) (K := K) (k' := k') (K' := K')) :
    ((k' ⊗[k] K) ⧸ nilradical (k' ⊗[k] K)) ≃ₐ[k'] K' :=
  (Ideal.quotientEquivAlgOfEq k' h.ker_eq_nilradical.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective h.surjective)

/-- The reduced tensor-product equivalence sends the class of a tensor element
to its canonical image in the top field. -/
theorem reducedTensorAlgEquiv_mk
    (h : Realization (k := k) (K := K) (k' := k') (K' := K'))
    (x : k' ⊗[k] K) :
    reducedTensorAlgEquiv h (Ideal.Quotient.mk _ x) =
      tensorProductMap (k := k) (K := K) (k' := k') (K' := K') x := sorry

/-- Lemma 10.45.3, tag `030R`: every essentially finite-type field extension
admits one finite purely inseparable realization in arbitrary requested
witness universes. -/
@[stacks 030R]
theorem existsOfEssFiniteType [Algebra.EssFiniteType k K] :
    ∃ (k' : Type (max u w)) (_ : Field k') (_ : Algebra k k')
      (K' : Type (max v (max u w))) (_ : Field K') (_ : Algebra k K') (_ : Algebra K K')
      (_ : Algebra k' K') (_ : IsScalarTower k K K') (_ : IsScalarTower k k' K'),
        Realization (k := k) (K := K) (k' := k') (K' := K') := sorry

end Realization

end

end FieldExtension.PurelyInseparable.Lift
