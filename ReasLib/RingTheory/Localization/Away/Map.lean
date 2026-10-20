/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of principal localizations

Mathlib defines the canonical ring map `Localization.awayMap`.  This leaf
records its composition law at the principal-localization interface, without
exposing the submonoid-containment witnesses used by `IsLocalization.map`.
-/

@[expose] public section

universe u v w

namespace Localization.Away

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommSemiring R] [CommSemiring S] [CommSemiring T]

/-- Canonical maps of principal localizations respect composition of ring homomorphisms. -/
@[stacks 051T "principal-localization map composition"]
theorem map_comp (f : R →+* S) (g : S →+* T) (r : R) :
    (Localization.awayMap g (f r)).comp (Localization.awayMap f r) =
      Localization.awayMap (g.comp f) r := sorry

/-- The principal-localization maps along a base algebra map followed by a subalgebra inclusion
compose to the canonical principal-localization map into the ambient algebra. -/
@[stacks 051T "principal-localization subalgebra map composition"]
theorem map_comp_subalgebra {A : Type u} {B : Type v}
    [CommSemiring A] [CommSemiring B] [Algebra A B]
    (T : Subalgebra A B) (a : A) :
    (Localization.awayMap T.val.toRingHom (algebraMap A T a)).comp
        (Localization.awayMap (algebraMap A T) a) =
      Localization.awayMap (algebraMap A B) a := sorry

/-- Tag `051T`: a canonical principal-localization map sends a coefficient class to the class
of its image. -/
@[simp, stacks 051T "principal-localization coefficient map"]
theorem map_apply_algebraMap (f : R →+* S) (r x : R) :
    Localization.awayMap f r (algebraMap R (Localization.Away r) x) =
      algebraMap S (Localization.Away (f r)) (f x) := sorry

/-- The algebra-hom owner of the canonical map from the localization away from `a` to the
localization away from `f * a`. -/
@[stacks 0BBI "multiplication map between principal localizations"]
noncomputable def mapMulₐ (a f : R) :
    Localization.Away a →ₐ[R] Localization.Away (f * a) :=
  IsLocalization.Away.liftAlgHom
    (S := Localization.Away a) (P := Localization.Away (f * a)) (A := R)
    (f := Algebra.ofId R (Localization.Away (f * a))) a
    (by
      change IsUnit (algebraMap R (Localization.Away (f * a)) a)
      exact IsLocalization.Away.isUnit_of_dvd
        (S := Localization.Away (f * a)) (x := f * a) (dvd_mul_left a f))

/-- The RingHom view of `mapMulₐ`; the algebra-hom definition remains the canonical owner. -/
@[stacks 0BBI "multiplication map ring-hom view"]
noncomputable abbrev mapMul (a f : R) :
    Localization.Away a →+* Localization.Away (f * a) :=
  (mapMulₐ a f).toRingHom

/-- The algebra-hom multiplication map agrees with the canonical coefficient maps. -/
@[simp, stacks 0BBI "multiplication algebra map coefficient law"]
theorem mapMulₐ_algebraMap (a f r : R) :
    mapMulₐ a f (algebraMap R (Localization.Away a) r) =
      algebraMap R (Localization.Away (f * a)) r := sorry

/-- The RingHom view of the multiplication map agrees with the canonical coefficient maps. -/
@[simp, stacks 0BBI "multiplication ring map coefficient law"]
theorem mapMul_algebraMap (a f r : R) :
    mapMul a f (algebraMap R (Localization.Away a) r) =
      algebraMap R (Localization.Away (f * a)) r := sorry

/-- The RingHom view is the underlying map of the canonical algebra hom. -/
@[simp, stacks 0BBI "multiplication map algebra-to-ring bridge"]
theorem mapMulₐ_toRingHom (a f : R) :
    (mapMulₐ a f).toRingHom = mapMul a f := sorry

/-- The multiplication map sends the standard class with denominator `a ^ n` to the class with
numerator `f ^ n * r` and denominator `(f * a) ^ n`. -/
@[simp, stacks 0BBI "multiplication map on principal-localization powers"]
theorem mapMul_mk_pow (a f : R) (n : ℕ) (r : R) :
    mapMul a f
        (Localization.mk r (Submonoid.pow a n)) =
      Localization.mk (f ^ n * r)
        (Submonoid.pow (f * a) n) := sorry

/-- Vanishing after the multiplication map is equivalent to annihilation by a power of `f` in
the source localization. -/
@[stacks 0BBI "multiplication map zero criterion"]
theorem mapMul_eq_zero_iff (a f : R) (z : Localization.Away a) :
    mapMul a f z = 0 ↔
      ∃ n : ℕ, (algebraMap R (Localization.Away a) f) ^ n * z = 0 := sorry

end Localization.Away
