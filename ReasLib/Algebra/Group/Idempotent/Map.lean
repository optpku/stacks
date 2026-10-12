/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Algebra.Ring.Equiv

/-!
# Maps of Idempotent Elements

This file provides the functorial action of multiplicative and ring homomorphisms on
the subtype of idempotent elements. The multiplicative API is the primary owner;
the `RingHom` API is its standard specialization.
-/

@[expose] public section

universe u v w

namespace MulHom

variable {M : Type u} {N : Type v} {P : Type w}
variable [Mul M] [Mul N] [Mul P]

/-- A multiplicative homomorphism maps idempotent elements to idempotent elements. -/
def idempotentMap (f : M →ₙ* N) :
    {e : M // IsIdempotentElem e} → {e : N // IsIdempotentElem e} :=
  fun e ↦ ⟨f e, e.2.map f⟩

/-- The underlying value of the image of an idempotent is the ordinary image under the
multiplicative homomorphism. -/
@[simp]
theorem idempotentMap_apply (f : M →ₙ* N) (e : {e : M // IsIdempotentElem e}) :
    ((f.idempotentMap e : {e : N // IsIdempotentElem e}) : N) = f e := sorry

/-- The identity multiplicative homomorphism acts identically on idempotent elements. -/
@[simp]
theorem idempotentMap_id_apply (e : {e : M // IsIdempotentElem e}) :
    (MulHom.id M).idempotentMap e = e := sorry

/-- Maps of idempotent elements respect composition of multiplicative homomorphisms. -/
@[simp]
theorem idempotentMap_comp_apply (g : N →ₙ* P) (f : M →ₙ* N)
    (e : {e : M // IsIdempotentElem e}) :
    (g.comp f).idempotentMap e = g.idempotentMap (f.idempotentMap e) := sorry

end MulHom

namespace MulEquiv

variable {M : Type u} {N : Type v}
variable [Mul M] [Mul N]

/-- The canonical idempotent map induced by a multiplicative equivalence has the inverse
map induced by the inverse equivalence as a left inverse. -/
theorem idempotentMap_leftInverse (e : M ≃* N) :
    Function.LeftInverse e.symm.toMulHom.idempotentMap e.toMulHom.idempotentMap := sorry

/-- The canonical idempotent map induced by a multiplicative equivalence has the inverse
map induced by the inverse equivalence as a right inverse. -/
theorem idempotentMap_rightInverse (e : M ≃* N) :
    Function.RightInverse e.symm.toMulHom.idempotentMap e.toMulHom.idempotentMap := sorry

/-- A multiplicative equivalence restricts to an equivalence between idempotent elements. -/
def idempotentEquiv (e : M ≃* N) :
    {x : M // IsIdempotentElem x} ≃ {x : N // IsIdempotentElem x} where
  toFun := e.toMulHom.idempotentMap
  invFun := e.symm.toMulHom.idempotentMap
  left_inv := idempotentMap_leftInverse e
  right_inv := idempotentMap_rightInverse e

/-- The forward map of `MulEquiv.idempotentEquiv` is the canonical idempotent map. -/
@[simp]
theorem idempotentEquiv_apply (e : M ≃* N) (x : {x : M // IsIdempotentElem x}) :
    e.idempotentEquiv x = e.toMulHom.idempotentMap x := sorry

/-- The inverse map of `MulEquiv.idempotentEquiv` is induced by the inverse multiplicative
equivalence. -/
@[simp]
theorem idempotentEquiv_symm_apply (e : M ≃* N) (x : {x : N // IsIdempotentElem x}) :
    e.idempotentEquiv.symm x = e.symm.toMulHom.idempotentMap x := sorry

/-- A multiplicative equivalence induces a bijection on idempotent elements. -/
theorem idempotentMap_bijective (e : M ≃* N) :
    Function.Bijective e.toMulHom.idempotentMap := sorry

end MulEquiv

namespace RingHom

variable {R : Type u} {S : Type v} {T : Type w}
variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring T]

/-- The canonical map on idempotents induced by a ring homomorphism. -/
def idempotentMap (f : R →+* S) :
    {e : R // IsIdempotentElem e} → {e : S // IsIdempotentElem e} :=
  f.toMonoidHom.toMulHom.idempotentMap

/-- The underlying value of a ring-homomorphic image of an idempotent is its ordinary
ring-homomorphic image. -/
@[simp]
theorem idempotentMap_apply (f : R →+* S) (e : {e : R // IsIdempotentElem e}) :
    ((f.idempotentMap e : {e : S // IsIdempotentElem e}) : S) = f e := sorry

/-- The identity ring homomorphism acts identically on idempotent elements. -/
@[simp]
theorem idempotentMap_id_apply (e : {e : R // IsIdempotentElem e}) :
    (RingHom.id R).idempotentMap e = e := sorry

/-- Maps of idempotent elements respect composition of ring homomorphisms. -/
@[simp]
theorem idempotentMap_comp_apply (g : S →+* T) (f : R →+* S)
    (e : {e : R // IsIdempotentElem e}) :
    (g.comp f).idempotentMap e = g.idempotentMap (f.idempotentMap e) := sorry

end RingHom

namespace RingEquiv

variable {R : Type u} {S : Type v}
variable [NonAssocSemiring R] [NonAssocSemiring S]

/-- A ring equivalence restricts to an equivalence between the idempotent elements of its
source and target. -/
def idempotentEquiv (e : R ≃+* S) :
    {x : R // IsIdempotentElem x} ≃ {x : S // IsIdempotentElem x} :=
  e.toMulEquiv.idempotentEquiv

/-- The forward map of `RingEquiv.idempotentEquiv` is the canonical idempotent map. -/
@[simp]
theorem idempotentEquiv_apply (e : R ≃+* S) (x : {x : R // IsIdempotentElem x}) :
    e.idempotentEquiv x = e.toRingHom.idempotentMap x := sorry

/-- The inverse map of `RingEquiv.idempotentEquiv` is induced by the inverse ring
equivalence. -/
@[simp]
theorem idempotentEquiv_symm_apply (e : R ≃+* S) (x : {x : S // IsIdempotentElem x}) :
    e.idempotentEquiv.symm x = e.symm.toRingHom.idempotentMap x := sorry

/-- A ring equivalence induces a bijection on idempotent elements. -/
theorem idempotentMap_bijective (e : R ≃+* S) :
    Function.Bijective e.toRingHom.idempotentMap := sorry

end RingEquiv
