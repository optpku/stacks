/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Torsion ideals under flat base change

This leaf owns the elementwise and finite-module annihilator comparisons for
a flat algebra map.  It is independent of associated-prime theory, so weak
association consumers can import it without importing a chapter file.
-/

open scoped TensorProduct

universe u v w

namespace Ideal

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S] [Module.Flat R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

/-- Extending the annihilator of `m` along a flat map agrees with the annihilator of
`1 ⊗ₜ[R] m` after tensor base change. -/
@[stacks 07T8 "element-annihilator assertion"]
theorem map_torsionOf_eq_baseChange_of_flat (m : M) :
    map (algebraMap R S) (torsionOf R M m) =
      torsionOf S (S ⊗[R] M) ((1 : S) ⊗ₜ[R] m) := sorry

end Ideal

namespace Module

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S] [Module.Flat R S]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- For a finite module, extending its annihilator along a flat map agrees with the
annihilator after base change. -/
@[stacks 07T8 "finite-module assertion"]
theorem map_annihilator_eq_baseChange_of_flat :
    Ideal.map (algebraMap R S) (annihilator R M) =
      annihilator S (S ⊗[R] M) := sorry

end Module

end
