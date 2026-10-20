/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite free ring homomorphisms

This file records the elementary ring-map property used by affine-local
finite-locally-free arguments: the target is a finite free module over the
source through the given map.
-/

@[expose] public section

universe u v

namespace RingHom

/-- A ring homomorphism is finite free when its target is finite and free as a module over its
source via the algebra structure induced by that homomorphism. -/
@[stacks 0DCR "finite-free ring maps in the free extension construction"]
def FiniteFree {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (f : R →+* A) : Prop :=
  -- Local instance justification (defeq pin): the induced algebra fixes the intended module action.
  let _ : Algebra R A := f.toAlgebra
  f.Finite ∧ Module.Free R A

/-- For an algebra structure map, finite freeness is exactly finite and free
module structure over the given base ring. -/
@[stacks 0DCR "finite-free algebra maps", simp]
theorem finiteFree_algebraMap {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A] :
    (algebraMap R A).FiniteFree ↔ Module.Finite R A ∧ Module.Free R A := by
  rw [FiniteFree, toAlgebra_algebraMap, RingHom.finite_algebraMap]
/- Proof strategy: unfold `RingHom.FiniteFree` using the induced algebra map
and discharge the equivalence with the canonical `Module.Finite`/`Module.Free`
instances. -/

end RingHom
