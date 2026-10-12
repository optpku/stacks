/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Free
public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.RingTheory.Flatness.MittagLeffler.TensorProduct

@[expose] public section

/-!
# Supporting Submodules of Tensors

@stack 059S
@stack 0AS6

The predicate `Submodule.SupportsTensor` names the recurring image condition for a tensor.  The
main API characterizes flat Mittag-Leffler modules by existence of least supporting submodules and
keeps the stronger finite-support theorem available independently.
-/

open scoped TensorProduct

universe u v w

namespace Submodule

section

variable {R : Type u} [CommSemiring R]
variable {F : Type v} {M : Type w}
variable [AddCommMonoid F] [Module R F] [AddCommMonoid M] [Module R M]

/-- A submodule supports a tensor when the tensor comes from its inclusion in the left factor. -/
@[stacks 059S "supporting submodule of a tensor"]
def SupportsTensor (N : Submodule R F) (x : F ⊗[R] M) : Prop :=
  x ∈ LinearMap.range (N.subtype.rTensor M)

/-- The supporting-submodule predicate unfolds to membership in the range of the tensorized
inclusion. -/
theorem supportsTensor_iff (N : Submodule R F) (x : F ⊗[R] M) :
    N.SupportsTensor x ↔ x ∈ LinearMap.range (N.subtype.rTensor M) := sorry

end

end Submodule

namespace Module.MittagLeffler

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {F : Type w} [AddCommGroup F] [Module R F]

/-- Chap10 Lemma 10 89 6 (Lemma 10.89.6), tag `0AS6`: every tensor over a flat
Mittag-Leffler module has a least supporting submodule, and that submodule is finite. -/
@[stacks 0AS6]
theorem exists_least_finite_tensorSupport [Module.Flat R M] [MittagLeffler R M]
    (x : F ⊗[R] M) :
    ∃ N : Submodule R F,
      IsLeast {N' : Submodule R F | N'.SupportsTensor x} N ∧ Module.Finite R N := sorry

/-- Chap10 Lemma 10 91 2, tag `059S`: a flat module is Mittag-Leffler exactly when every tensor
over a finite free module has a least supporting submodule. -/
@[stacks 059S]
theorem iff_exists_least_tensorSupport [Module.Flat R M] :
    MittagLeffler R M ↔
      ∀ (F : ModuleCat.{max u w} R) [Module.Free R F] [Module.Finite R F]
        (x : F ⊗[R] M),
        ∃ N : Submodule R F, IsLeast {N' : Submodule R F | N'.SupportsTensor x} N := sorry

/-- A flat Mittag-Leffler module supplies a least supporting submodule for every tensor over a
finite free module. -/
theorem exists_least_tensorSupport [Module.Flat R M] [MittagLeffler R M]
    (F : ModuleCat.{max u w} R) [Module.Free R F] [Module.Finite R F]
    (x : F ⊗[R] M) :
    ∃ N : Submodule R F, IsLeast {N' : Submodule R F | N'.SupportsTensor x} N := sorry

/-- A flat module with least supporting submodules for tensors over finite free modules is
Mittag-Leffler. -/
theorem of_exists_least_tensorSupport [Module.Flat R M]
    (h : ∀ (F : ModuleCat.{max u w} R) [Module.Free R F] [Module.Finite R F]
      (x : F ⊗[R] M),
      ∃ N : Submodule R F, IsLeast {N' : Submodule R F | N'.SupportsTensor x} N) :
    MittagLeffler R M := sorry

end

end Module.MittagLeffler
