/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import ReasLib.CategoryTheory.Monoidal.Tor
import StacksCheckRecall

@[expose] public section

/-!
# Remark 10.75.6
@stack 00M4

The braided `Tor` symmetry is owned by `CategoryTheory.torFlipIso`. The chapter records its
degree-zero tensor interpretation, the eigenspaces of the tensor switch, its failure to be
semisimple in characteristic two, and the fact that changing the sign does not produce a
universal identity.
-/

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory ModuleCat.MonoidalCategory

universe u v

section

variable {R : Type u} [CommRing R]

/-- In degree zero, the diagonal `Tor` symmetry agrees with the tensor-product braiding after the
canonical comparisons between the degree-zero derived functors and tensor product. -/
@[stacks 00M4 "degree-zero braiding identification"]
theorem tor_zero_self_flip_via_tensor_braiding (M : ModuleCat R) :
    ((tensorLeft M).leftDerivedZeroIsoSelf.inv.app M) ≫
        ((torFlipIso (ModuleCat R) 0).app M).hom.app M ≫
        (tensorRight M).fromLeftDerivedZero.app M =
      (β_ M M).hom := sorry

end


section

variable {k : Type u} [Field k]

/-- On the free rank-two module over a field, the diagonal degree-zero `Tor` symmetry is not the
identity. -/
@[stacks 00M4 "free rank-two counterexample"]
theorem tor_zero_self_flip_not_identity_on_free_rankTwo :
    ((tensorLeft (ModuleCat.of k (k × k))).leftDerivedZeroIsoSelf.inv.app
        (ModuleCat.of k (k × k))) ≫
        ((torFlipIso (ModuleCat k) 0).app (ModuleCat.of k (k × k))).hom.app
          (ModuleCat.of k (k × k)) ≫
        (tensorRight (ModuleCat.of k (k × k))).fromLeftDerivedZero.app
          (ModuleCat.of k (k × k)) ≠
      𝟙 ((ModuleCat.of k (k × k)) ⊗ (ModuleCat.of k (k × k))) := sorry

/-- Remark 10.75.6 (1): the canonical diagonal symmetry of `Tor_i^R(M, M)` is not universally
the identity; this already fails in degree zero for a free rank-two module. -/
@[stacks 00M4 "(1)"]
theorem tor_zero_self_flip_not_universally_identity :
    ¬ ∀ M : ModuleCat k,
      ((tensorLeft M).leftDerivedZeroIsoSelf.inv.app M) ≫
          ((torFlipIso (ModuleCat k) 0).app M).hom.app M ≫
          (tensorRight M).fromLeftDerivedZero.app M =
        𝟙 (M ⊗ M) := sorry

end


namespace TensorProduct

section

variable {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- Remark 10.75.6 (2): when `2 ≠ 0`, the `1`- and `-1`-eigenspaces of the switch on
`V ⊗[k] V` have dimensions `(n² + n) / 2` and `(n² - n) / 2`, respectively, where
`n = Module.finrank k V`. -/
@[stacks 00M4 "(2)"]
theorem commEigenspaceFinrank (h2 : (2 : k) ≠ 0) :
    Module.finrank k
        (Module.End.eigenspace (TensorProduct.comm k V V).toLinearMap (1 : k)) =
        (Module.finrank k V ^ 2 + Module.finrank k V) / 2 ∧
      Module.finrank k
          (Module.End.eigenspace (TensorProduct.comm k V V).toLinearMap (-1 : k)) =
        (Module.finrank k V ^ 2 - Module.finrank k V) / 2 := sorry

section

variable [CharP k 2]

/-- Remark 10.75.6 (3): in characteristic two, the tensor switch on a vector space of dimension
at least two is not semisimple, hence is not diagonalizable. -/
@[stacks 00M4 "(3)"]
theorem commNotIsSemisimpleOfCharTwo (hV : 2 ≤ Module.finrank k V) :
    ¬ Module.End.IsSemisimple (TensorProduct.comm k V V).toLinearMap := sorry

end


end


end TensorProduct


section


variable {k : Type u} [Field k]

/-- Remark 10.75.6 (4): negating the canonical diagonal degree-zero `Tor` symmetry does not make
it universally equal to the identity. -/
@[stacks 00M4 "(4)"]
theorem torZeroNegSelfFlipNotUniversallyIdentity :
    ¬ ∀ M : ModuleCat k,
      -(((tensorLeft M).leftDerivedZeroIsoSelf.inv.app M) ≫
          ((torFlipIso (ModuleCat k) 0).app M).hom.app M ≫
          (tensorRight M).fromLeftDerivedZero.app M) =
        𝟙 (M ⊗ M) := sorry

end


@[stacks 00M4 "braided Tor symmetry owner"]
#check @CategoryTheory.torFlipIso

@[stacks 00M4 "degree-zero tensor interpretation"]
#check @tor_zero_self_flip_via_tensor_braiding

@[stacks 00M4 "nonidentity counterexample"]
#check @tor_zero_self_flip_not_universally_identity

@[stacks 00M4 "switch eigenspace dimensions"]
#check @TensorProduct.commEigenspaceFinrank

@[stacks 00M4 "characteristic-two nonsemisimplicity"]
#check @TensorProduct.commNotIsSemisimpleOfCharTwo

@[stacks 00M4 "changing the sign does not give the identity"]
#check @torZeroNegSelfFlipNotUniversallyIdentity

end
