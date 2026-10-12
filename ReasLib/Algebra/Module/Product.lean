/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Modules over Product Semirings

This file contains the algebraic, category-independent part of the decomposition of a module over
a product semiring.  The componentwise action is deliberately an explicit non-instance owner:
when both factors already carry an action of the product semiring, Mathlib's ordinary product
module instance describes a different action.
-/

@[expose] public section

universe u v w x

namespace Module.Product

variable (R : Type u) (S : Type v) [Semiring R] [Semiring S]

/-- The left idempotent `(1, 0)` of the product semiring `R × S`. -/
@[stacks 00JH "product semiring left idempotent"]
def leftIdempotent : R × S :=
  (1, 0)

/-- The right idempotent `(0, 1)` of the product semiring `R × S`. -/
@[stacks 00JH "product semiring right idempotent"]
def rightIdempotent : R × S :=
  (0, 1)

/-- The left idempotent is central in the product semiring. -/
@[stacks 00JH "product semiring left idempotent centrality"]
theorem leftIdempotent_comm (a : R × S) :
    leftIdempotent R S * a = a * leftIdempotent R S := by
  ext <;> simp [leftIdempotent]

/-- The right idempotent is central in the product semiring. -/
@[stacks 00JH "product semiring right idempotent centrality"]
theorem rightIdempotent_comm (a : R × S) :
    rightIdempotent R S * a = a * rightIdempotent R S := by
  ext <;> simp [rightIdempotent]

/-- The left product idempotent is idempotent. -/
@[simp, stacks 00JH "product semiring left idempotent law"]
theorem leftIdempotent_mul_self :
    leftIdempotent R S * leftIdempotent R S = leftIdempotent R S := by
  ext <;> simp [leftIdempotent]

/-- The right product idempotent is idempotent. -/
@[simp, stacks 00JH "product semiring right idempotent law"]
theorem rightIdempotent_mul_self :
    rightIdempotent R S * rightIdempotent R S = rightIdempotent R S := by
  ext <;> simp [rightIdempotent]

/-- The two product idempotents are orthogonal in the indicated order. -/
@[simp, stacks 00JH "product semiring left right orthogonality"]
theorem leftIdempotent_mul_rightIdempotent :
    leftIdempotent R S * rightIdempotent R S = 0 := by
  ext <;> simp [leftIdempotent, rightIdempotent]

/-- The two product idempotents are orthogonal in the opposite order. -/
@[simp, stacks 00JH "product semiring right left orthogonality"]
theorem rightIdempotent_mul_leftIdempotent :
    rightIdempotent R S * leftIdempotent R S = 0 := by
  ext <;> simp [leftIdempotent, rightIdempotent]

/-- The two complementary product idempotents sum to one. -/
@[simp, stacks 00JH "product semiring complementary idempotents"]
theorem leftIdempotent_add_rightIdempotent :
    leftIdempotent R S + rightIdempotent R S = 1 := by
  ext <;> simp [leftIdempotent, rightIdempotent]

/-- The left factor of an `(R × S)`-module, characterized by annihilation by `(0, 1)`. -/
@[stacks 00JH "product semiring left module factor"]
def leftSubmodule (M : Type w) [AddCommMonoid M] [Module (R × S) M] :
    Submodule (R × S) M where
  carrier := {m | rightIdempotent R S • m = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change rightIdempotent R S • (x + y) = 0
    change rightIdempotent R S • x = 0 at hx
    change rightIdempotent R S • y = 0 at hy
    rw [smul_add, hx, hy, add_zero]
  smul_mem' := by
    intro a x hx
    change rightIdempotent R S • (a • x) = 0
    change rightIdempotent R S • x = 0 at hx
    rw [smul_smul, rightIdempotent_comm, ← smul_smul, hx, smul_zero]

/-- Membership in the left factor is annihilation by the right idempotent. -/
@[simp, stacks 00JH "product semiring left factor membership"]
theorem mem_leftSubmodule_iff (M : Type w) [AddCommMonoid M] [Module (R × S) M]
    (m : M) :
    m ∈ leftSubmodule R S M ↔ rightIdempotent R S • m = 0 :=
  Iff.rfl

/-- The right factor of an `(R × S)`-module, characterized by annihilation by `(1, 0)`. -/
@[stacks 00JH "product semiring right module factor"]
def rightSubmodule (M : Type w) [AddCommMonoid M] [Module (R × S) M] :
    Submodule (R × S) M where
  carrier := {m | leftIdempotent R S • m = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change leftIdempotent R S • (x + y) = 0
    change leftIdempotent R S • x = 0 at hx
    change leftIdempotent R S • y = 0 at hy
    rw [smul_add, hx, hy, add_zero]
  smul_mem' := by
    intro a x hx
    change leftIdempotent R S • (a • x) = 0
    change leftIdempotent R S • x = 0 at hx
    rw [smul_smul, leftIdempotent_comm, ← smul_smul, hx, smul_zero]

/-- Membership in the right factor is annihilation by the left idempotent. -/
@[simp, stacks 00JH "product semiring right factor membership"]
theorem mem_rightSubmodule_iff (M : Type w) [AddCommMonoid M] [Module (R × S) M]
    (m : M) :
    m ∈ rightSubmodule R S M ↔ leftIdempotent R S • m = 0 :=
  Iff.rfl

/-- The left factor of a product-semiring module has its canonical `R`-module structure. -/
@[stacks 00JH "product semiring left factor module structure"]
instance leftModule (M : Type w) [AddCommMonoid M] [Module (R × S) M] :
    Module R (leftSubmodule R S M) where
  smul r m := ⟨((r, (0 : S)) : R × S) • m.1, by
    change rightIdempotent R S • (((r, (0 : S)) : R × S) • m.1) = 0
    rw [smul_smul]
    have hzero : rightIdempotent R S * ((r, (0 : S)) : R × S) = 0 := by
      ext <;> simp [rightIdempotent]
    rw [hzero]
    exact zero_smul (R × S) m.1⟩
  one_smul := by
    intro m
    apply Subtype.ext
    change (((1 : R), (0 : S)) : R × S) • m.1 = m.1
    have hm : (((0 : R), (1 : S)) : R × S) • m.1 = 0 := m.property
    calc
      (((1 : R), (0 : S)) : R × S) • m.1 =
          (((1 : R), (0 : S)) : R × S) • m.1 +
            (((0 : R), (1 : S)) : R × S) • m.1 := by rw [hm, add_zero]
      _ = ((((1 : R), (0 : S)) : R × S) + ((0, 1) : R × S)) • m.1 :=
        (add_smul ((1, 0) : R × S) ((0, 1) : R × S) m.1).symm
      _ = m.1 := by
        rw [show (((1, 0) : R × S) + (0, 1)) = 1 by ext <;> simp, one_smul]
  mul_smul := by
    intro r s m
    apply Subtype.ext
    change (((r * s, (0 : S)) : R × S) • m.1) =
      ((r, (0 : S)) : R × S) • (((s, (0 : S)) : R × S) • m.1)
    rw [show ((r * s, (0 : S)) : R × S) = (r, 0) * (s, 0) by ext <;> simp]
    exact mul_smul ((r, 0) : R × S) ((s, 0) : R × S) m.1
  smul_zero := by
    intro r
    apply Subtype.ext
    change (((r, (0 : S)) : R × S) • (0 : M)) = 0
    exact smul_zero _
  smul_add := by
    intro r m n
    apply Subtype.ext
    change (((r, (0 : S)) : R × S) • (m.1 + n.1)) =
      ((r, (0 : S)) : R × S) • m.1 + ((r, (0 : S)) : R × S) • n.1
    exact smul_add _ _ _
  zero_smul := by
    intro m
    apply Subtype.ext
    change (((0 : R), (0 : S)) : R × S) • m.1 = 0
    exact zero_smul (R × S) m.1
  add_smul := by
    intro r s m
    apply Subtype.ext
    change (((r + s, (0 : S)) : R × S) • m.1) =
      ((r, (0 : S)) : R × S) • m.1 + ((s, (0 : S)) : R × S) • m.1
    rw [show ((r + s, (0 : S)) : R × S) = (r, 0) + (s, 0) by ext <;> simp]
    exact add_smul ((r, 0) : R × S) ((s, 0) : R × S) m.1

/-- The canonical left-factor scalar action is multiplication by `(r, 0)` in the ambient module.
-/
@[simp, stacks 00JH "product semiring left factor scalar action"]
theorem leftModule_smul_val (M : Type w) [AddCommMonoid M] [Module (R × S) M]
    (r : R) (m : leftSubmodule R S M) :
    (r • m).1 = ((r, (0 : S)) : R × S) • m.1 := by
  rfl

/-- On the left factor, the ambient product-semiring action only uses the first coordinate. -/
@[simp, stacks 00JH "product semiring left factor ambient scalar action"]
theorem leftSubmodule_smul_val (M : Type w) [AddCommMonoid M] [Module (R × S) M]
    (a : R × S) (m : leftSubmodule R S M) :
    a • m.1 = (a.1 • m).1 := by
  rw [leftModule_smul_val]
  have hright : (((0 : R), a.2) : R × S) • m.1 = 0 := by
    calc
      (((0 : R), a.2) : R × S) • m.1 =
          ((((0 : R), a.2) : R × S) * rightIdempotent R S) • m.1 := by
            congr 1
            ext <;> simp [rightIdempotent]
      _ = (((0 : R), a.2) : R × S) • (rightIdempotent R S • m.1) := by
            rw [mul_smul]
      _ = 0 := by rw [m.property, smul_zero]
  calc
    a • m.1 = (((a.1, (0 : S)) : R × S) + (0, a.2)) • m.1 := by
      congr 1
      ext <;> simp
    _ = ((a.1, (0 : S)) : R × S) • m.1 + ((0, a.2) : R × S) • m.1 := by
      rw [add_smul]
    _ = ((a.1, (0 : S)) : R × S) • m.1 := by rw [hright, add_zero]

/-- The right factor of a product-semiring module has its canonical `S`-module structure. -/
@[stacks 00JH "product semiring right factor module structure"]
instance rightModule (M : Type w) [AddCommMonoid M] [Module (R × S) M] :
    Module S (rightSubmodule R S M) where
  smul s m := ⟨(((0 : R), s) : R × S) • m.1, by
    change leftIdempotent R S • ((((0 : R), s) : R × S) • m.1) = 0
    rw [smul_smul]
    have hzero : leftIdempotent R S * (((0 : R), s) : R × S) = 0 := by
      ext <;> simp [leftIdempotent]
    rw [hzero]
    exact zero_smul (R × S) m.1⟩
  one_smul := by
    intro m
    apply Subtype.ext
    change (((0 : R), (1 : S)) : R × S) • m.1 = m.1
    have hm : (((1 : R), (0 : S)) : R × S) • m.1 = 0 := m.property
    calc
      (((0 : R), (1 : S)) : R × S) • m.1 =
          (((1 : R), (0 : S)) : R × S) • m.1 +
            (((0 : R), (1 : S)) : R × S) • m.1 := by rw [hm, zero_add]
      _ = ((((1 : R), (0 : S)) : R × S) + ((0, 1) : R × S)) • m.1 :=
        (add_smul ((1, 0) : R × S) ((0, 1) : R × S) m.1).symm
      _ = m.1 := by
        rw [show (((1, 0) : R × S) + (0, 1)) = 1 by ext <;> simp, one_smul]
  mul_smul := by
    intro r s m
    apply Subtype.ext
    change ((((0 : R), r * s) : R × S) • m.1) =
      (((0 : R), r) : R × S) • ((((0 : R), s) : R × S) • m.1)
    rw [show (((0 : R), r * s) : R × S) = (0, r) * (0, s) by ext <;> simp]
    exact mul_smul ((0, r) : R × S) ((0, s) : R × S) m.1
  smul_zero := by
    intro r
    apply Subtype.ext
    change ((((0 : R), r) : R × S) • (0 : M)) = 0
    exact smul_zero _
  smul_add := by
    intro r m n
    apply Subtype.ext
    change ((((0 : R), r) : R × S) • (m.1 + n.1)) =
      (((0 : R), r) : R × S) • m.1 + (((0 : R), r) : R × S) • n.1
    exact smul_add _ _ _
  zero_smul := by
    intro m
    apply Subtype.ext
    change (((0 : R), (0 : S)) : R × S) • m.1 = 0
    exact zero_smul (R × S) m.1
  add_smul := by
    intro r s m
    apply Subtype.ext
    change ((((0 : R), r + s) : R × S) • m.1) =
      (((0 : R), r) : R × S) • m.1 + (((0 : R), s) : R × S) • m.1
    rw [show (((0 : R), r + s) : R × S) = (0, r) + (0, s) by ext <;> simp]
    exact add_smul ((0, r) : R × S) ((0, s) : R × S) m.1

/-- The canonical right-factor scalar action is multiplication by `(0, s)` in the ambient
module. -/
@[simp, stacks 00JH "product semiring right factor scalar action"]
theorem rightModule_smul_val (M : Type w) [AddCommMonoid M] [Module (R × S) M]
    (s : S) (m : rightSubmodule R S M) :
    (s • m).1 = (((0 : R), s) : R × S) • m.1 := by
  rfl

/-- On the right factor, the ambient product-semiring action only uses the second coordinate. -/
@[simp, stacks 00JH "product semiring right factor ambient scalar action"]
theorem rightSubmodule_smul_val (M : Type w) [AddCommMonoid M] [Module (R × S) M]
    (a : R × S) (m : rightSubmodule R S M) :
    a • m.1 = (a.2 • m).1 := by
  rw [rightModule_smul_val]
  have hleft : ((a.1, (0 : S)) : R × S) • m.1 = 0 := by
    calc
      ((a.1, (0 : S)) : R × S) • m.1 =
          (((a.1, (0 : S)) : R × S) * leftIdempotent R S) • m.1 := by
            congr 1
            ext <;> simp [leftIdempotent]
      _ = ((a.1, (0 : S)) : R × S) • (leftIdempotent R S • m.1) := by
            rw [mul_smul]
      _ = 0 := by rw [m.property, smul_zero]
  calc
    a • m.1 = (((a.1, (0 : S)) : R × S) + (0, a.2)) • m.1 := by
      congr 1
      ext <;> simp
    _ = ((a.1, (0 : S)) : R × S) • m.1 + ((0, a.2) : R × S) • m.1 := by
      rw [add_smul]
    _ = ((0, a.2) : R × S) • m.1 := by rw [hleft, zero_add]

/-- Multiplication by the left idempotent is an endomorphism of a product-semiring module. -/
@[stacks 00JH "product semiring left projector"]
def leftProjection (M : Type w) [AddCommMonoid M] [Module (R × S) M] :
    M →ₗ[(R × S)] M where
  toFun m := leftIdempotent R S • m
  map_add' := smul_add _
  map_smul' := by
    intro a m
    simp [smul_smul, leftIdempotent_comm]

/-- Multiplication by the right idempotent is an endomorphism of a product-semiring module. -/
@[stacks 00JH "product semiring right projector"]
def rightProjection (M : Type w) [AddCommMonoid M] [Module (R × S) M] :
    M →ₗ[(R × S)] M where
  toFun m := rightIdempotent R S • m
  map_add' := smul_add _
  map_smul' := by
    intro a m
    simp [smul_smul, rightIdempotent_comm]

/-- The left projector evaluates by multiplication with `(1, 0)`. -/
@[simp, stacks 00JH "product semiring left projector evaluation"]
theorem leftProjection_apply (M : Type w) [AddCommMonoid M] [Module (R × S) M]
    (m : M) :
    leftProjection R S M m = leftIdempotent R S • m :=
  rfl

/-- The right projector evaluates by multiplication with `(0, 1)`. -/
@[simp, stacks 00JH "product semiring right projector evaluation"]
theorem rightProjection_apply (M : Type w) [AddCommMonoid M] [Module (R × S) M]
    (m : M) :
    rightProjection R S M m = rightIdempotent R S • m :=
  rfl

/-- The left factor is the kernel of the right projector. -/
@[stacks 00JH "product semiring left factor kernel"]
theorem leftSubmodule_eq_ker_rightProjection (M : Type w) [AddCommMonoid M]
    [Module (R × S) M] :
    leftSubmodule R S M = LinearMap.ker (rightProjection R S M) :=
  rfl

/-- The right factor is the kernel of the left projector. -/
@[stacks 00JH "product semiring right factor kernel"]
theorem rightSubmodule_eq_ker_leftProjection (M : Type w) [AddCommMonoid M]
    [Module (R × S) M] :
    rightSubmodule R S M = LinearMap.ker (leftProjection R S M) :=
  rfl

/-- Every element splits as the sum of its two idempotent components. -/
@[stacks 00JH "product semiring module factor decomposition"]
theorem left_smul_add_right_smul (M : Type w) [AddCommMonoid M] [Module (R × S) M]
    (m : M) :
    leftIdempotent R S • m + rightIdempotent R S • m = m := by
  rw [← add_smul, leftIdempotent_add_rightIdempotent, one_smul]

/-- The additive equivalence between a product-semiring module and its two idempotent factors.
-/
@[stacks 00JH "product semiring module factor additive equivalence"]
def factorAddEquiv (M : Type w) [AddCommMonoid M] [Module (R × S) M] :
    M ≃+ leftSubmodule R S M × rightSubmodule R S M where
  toFun m :=
    ( ⟨leftIdempotent R S • m, by
        change rightIdempotent R S • (leftIdempotent R S • m) = 0
        rw [smul_smul, rightIdempotent_mul_leftIdempotent, zero_smul]⟩
    , ⟨rightIdempotent R S • m, by
        change leftIdempotent R S • (rightIdempotent R S • m) = 0
        rw [smul_smul, leftIdempotent_mul_rightIdempotent, zero_smul]⟩ )
  invFun x := x.1.1 + x.2.1
  left_inv := left_smul_add_right_smul R S M
  right_inv := by
    rintro ⟨l, r⟩
    apply Prod.ext
    · apply Subtype.ext
      change leftIdempotent R S • (l.1 + r.1) = l.1
      have hl := left_smul_add_right_smul R S M l.1
      rw [l.property, add_zero] at hl
      have hr0 : leftIdempotent R S • r.1 = 0 := r.property
      rw [smul_add, hl, hr0, add_zero]
    · apply Subtype.ext
      change rightIdempotent R S • (l.1 + r.1) = r.1
      have hr := left_smul_add_right_smul R S M r.1
      rw [r.property, zero_add] at hr
      have hl0 : rightIdempotent R S • l.1 = 0 := l.property
      rw [smul_add, hl0, hr, zero_add]
  map_add' := by
    intro m n
    apply Prod.ext
    · apply Subtype.ext
      change leftIdempotent R S • (m + n) =
        leftIdempotent R S • m + leftIdempotent R S • n
      exact smul_add _ _ _
    · apply Subtype.ext
      change rightIdempotent R S • (m + n) =
        rightIdempotent R S • m + rightIdempotent R S • n
      exact smul_add _ _ _

/-- The idempotent factor decomposition as an equivalence of `(R × S)`-modules. -/
@[stacks 00JH "product semiring module factor linear equivalence"]
def factorLinearEquiv (M : Type w) [AddCommMonoid M] [Module (R × S) M] :
    M ≃ₗ[R × S] leftSubmodule R S M × rightSubmodule R S M :=
  { factorAddEquiv R S M with
    map_smul' := by
      intro a m
      apply Prod.ext
      · apply Subtype.ext
        change leftIdempotent R S • (a • m) = a • (leftIdempotent R S • m)
        rw [smul_smul, smul_smul, leftIdempotent_comm]
      · apply Subtype.ext
        change rightIdempotent R S • (a • m) = a • (rightIdempotent R S • m)
        rw [smul_smul, smul_smul, rightIdempotent_comm] }

/-- The first component of `factorAddEquiv` is the left idempotent component. -/
@[simp, stacks 00JH "product semiring factor additive equivalence left evaluation"]
theorem factorAddEquiv_apply_left (M : Type w) [AddCommMonoid M] [Module (R × S) M]
    (m : M) :
    ((factorAddEquiv R S M m).1).1 = leftIdempotent R S • m := by
  change leftIdempotent R S • m = _
  rfl

/-- The second component of `factorAddEquiv` is the right idempotent component. -/
@[simp, stacks 00JH "product semiring factor additive equivalence right evaluation"]
theorem factorAddEquiv_apply_right (M : Type w) [AddCommMonoid M] [Module (R × S) M]
    (m : M) :
    ((factorAddEquiv R S M m).2).1 = rightIdempotent R S • m := by
  change rightIdempotent R S • m = _
  rfl

/-- The inverse of `factorAddEquiv` adds the two factor elements. -/
@[simp, stacks 00JH "product semiring factor additive equivalence inverse evaluation"]
theorem factorAddEquiv_symm_apply (M : Type w) [AddCommMonoid M] [Module (R × S) M]
    (x : leftSubmodule R S M × rightSubmodule R S M) :
    (factorAddEquiv R S M).symm x = x.1.1 + x.2.1 := by
  change x.1.1 + x.2.1 = _
  rfl

/-- The componentwise `(R × S)`-module structure on the product of an `R`-module and an
`S`-module.  This is not an instance, so users can select it explicitly without creating an
action diamond with `Prod.instModule`. -/
@[reducible, stacks 00JH "product semiring componentwise module structure"]
def componentwise (M : Type w) (N : Type x) [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module S N] : Module (R × S) (M × N) where
  smul r m := (r.1 • m.1, r.2 • m.2)
  one_smul := by
    intro m
    change ((1 : R) • m.1, (1 : S) • m.2) = m
    ext <;> simp
  mul_smul := by
    intro a b m
    change ((a.1 * b.1) • m.1, (a.2 * b.2) • m.2) =
      (a.1 • b.1 • m.1, a.2 • b.2 • m.2)
    ext <;> simp [mul_smul]
  smul_zero := by
    intro a
    change (a.1 • (0 : M), a.2 • (0 : N)) = 0
    ext <;> simp
  smul_add := by
    intro a m n
    change (a.1 • (m.1 + n.1), a.2 • (m.2 + n.2)) =
      (a.1 • m.1 + a.1 • n.1, a.2 • m.2 + a.2 • n.2)
    ext <;> simp [smul_add]
  add_smul := by
    intro a b m
    change ((a.1 + b.1) • m.1, (a.2 + b.2) • m.2) =
      (a.1 • m.1 + b.1 • m.1, a.2 • m.2 + b.2 • m.2)
    ext <;> simp [add_smul]
  zero_smul := by
    intro m
    change (((0 : R) • m.1), ((0 : S) • m.2)) = 0
    ext <;> simp

/-- The idempotent factor decomposition, with the codomain equipped with the explicit
componentwise product-ring action. -/
@[stacks 00JH "product semiring componentwise factor linear equivalence"]
def factorComponentwiseLinearEquiv (M : Type w) [AddCommMonoid M] [Module (R × S) M] :
    -- Local instance justification (defeq pin): the factor decomposition has this componentwise action.
    letI : Module (R × S) (leftSubmodule R S M × rightSubmodule R S M) :=
      componentwise R S (leftSubmodule R S M) (rightSubmodule R S M)
    M ≃ₗ[R × S] leftSubmodule R S M × rightSubmodule R S M := by
  -- Local instance justification (defeq pin): retain the action fixed by the codomain type.
  letI : Module (R × S) (leftSubmodule R S M × rightSubmodule R S M) :=
    componentwise R S (leftSubmodule R S M) (rightSubmodule R S M)
  exact
    { factorAddEquiv R S M with
      map_smul' := by
        intro a m
        apply Prod.ext
        · apply Subtype.ext
          change leftIdempotent R S • (a • m) =
            ((a.1, (0 : S)) : R × S) • (leftIdempotent R S • m)
          rw [smul_smul, smul_smul]
          congr 1
          ext <;> simp [leftIdempotent]
        · apply Subtype.ext
          change rightIdempotent R S • (a • m) =
            (((0 : R), a.2) : R × S) • (rightIdempotent R S • m)
          rw [smul_smul, smul_smul]
          congr 1
          ext <;> simp [rightIdempotent] }

end Module.Product
