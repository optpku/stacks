module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor-product base change of ring homomorphisms

This leaf provides the ring-hom presentation of the canonical tensor-product inclusion.  It keeps
the algebra structures induced by the two ring homomorphisms internal, so consumers need not
reinstall them with local instances.

@stack 0BR6
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The canonical tensor-product base change of `f : R →+* S` along `g : R →+* R'`.
This is the ring-hom view of `Algebra.TensorProduct.includeLeft`; it is the shared owner for
base-change statements that are naturally phrased without ambient `Algebra` instances. -/
@[stacks 0BR6]
abbrev baseChange {R' : Type w} [CommRing R'] (f : R →+* S) (g : R →+* R') :
    let _ : Algebra R S := f.toAlgebra
    let _ : Algebra R R' := g.toAlgebra
    R' →+* R' ⊗[R] S :=
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra R R' := g.toAlgebra
  algebraMap R' (R' ⊗[R] S)

/-- The explicit-map base change sends `x : R'` to the left tensor-product inclusion.
The local algebra structures are exactly those selected by `f` and `g`. -/
@[simp, stacks 0BR6 "explicit base-change map computation"]
theorem baseChange_apply {R' : Type w} [CommRing R']
    (f : R →+* S) (g : R →+* R') (x : R') :
    let _ : Algebra R S := f.toAlgebra
    let _ : Algebra R R' := g.toAlgebra
    baseChange f g x =
      (Algebra.TensorProduct.includeLeft (R := R) (S := R') (A := R') (B := S)) x := sorry

/-- The canonical base-change map along an existing `Algebra R R'` instance.
This owner preserves the ambient tensor-product instance on `R'`; it deliberately
installs the canonical algebra induced by `f` on `S`. When an ambient `Algebra R S`
is already available, prefer the direct `algebraMap R' (R' ⊗[R] S)` presentation. -/
@[stacks 0BR6]
abbrev baseChangeAlgebraMap {R' : Type w} [CommRing R'] [Algebra R R'] (f : R →+* S) :
    let _ : Algebra R S := f.toAlgebra
    R' →+* R' ⊗[R] S :=
  let _ : Algebra R S := f.toAlgebra
  algebraMap R' (R' ⊗[R] S)

/-- The ambient-algebra base change sends `x : R'` to the left tensor-product inclusion.
Only the algebra structure on `S` is selected from the explicit map `f`. -/
@[simp, stacks 0BR6 "ambient-algebra base-change map computation"]
theorem baseChangeAlgebraMap_apply {R' : Type w} [CommRing R'] [Algebra R R']
    (f : R →+* S) (x : R') :
    let _ : Algebra R S := f.toAlgebra
    baseChangeAlgebraMap f x =
      (Algebra.TensorProduct.includeLeft (R := R) (S := R') (A := R') (B := S)) x := sorry

end RingHom
