/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.BaseChange
public import ReasLib.LinearAlgebra.ExteriorAlgebra.BaseChange
public import ReasLib.LinearAlgebra.SymmetricAlgebra.BaseChange
public import ReasLib.LinearAlgebra.TensorAlgebra.BaseChange
import StacksCheckRecall

/-!
# Localization of tensor, symmetric, and exterior algebras

@stack 0C6F

The shared owners are stated for an arbitrary `IsBaseChange`; this file specializes them to the
canonical localized-module model.
-/

@[expose] public section

open scoped TensorProduct

universe u v

section Semiring

variable {R : Type u} [CommSemiring R]
variable (S : Submonoid R)
variable {M : Type v} [AddCommMonoid M] [Module R M]

@[stacks 0C6F "(1), tensor algebra"]
#check ((LocalizedModule.isBaseChange S M).tensorAlgebraEquiv.symm :
  TensorAlgebra (Localization S) (LocalizedModule S M) ≃ₐ[Localization S]
    Localization S ⊗[R] TensorAlgebra R M)

@[stacks 0C6F "(1), tensor algebra generator"]
#check (fun x : LocalizedModule S M ↦
  (LocalizedModule.isBaseChange S M).tensorAlgebraEquiv_symm_apply_ι x :
    ∀ x : LocalizedModule S M,
      (LocalizedModule.isBaseChange S M).tensorAlgebraEquiv.symm
          (TensorAlgebra.ι (Localization S) x) =
        (TensorAlgebra.ι R).baseChange (Localization S)
          ((LocalizedModule.isBaseChange S M).equiv.symm x))

@[stacks 0C6F "(2), symmetric algebra"]
#check ((LocalizedModule.isBaseChange S M).symmetricAlgebraEquiv.symm :
  SymmetricAlgebra (Localization S) (LocalizedModule S M) ≃ₐ[Localization S]
    Localization S ⊗[R] SymmetricAlgebra R M)

@[stacks 0C6F "(2), symmetric algebra generator"]
#check (fun x : LocalizedModule S M ↦
  (LocalizedModule.isBaseChange S M).symmetricAlgebraEquiv_symm_apply_ι x :
    ∀ x : LocalizedModule S M,
      (LocalizedModule.isBaseChange S M).symmetricAlgebraEquiv.symm
          (SymmetricAlgebra.ι (Localization S) (LocalizedModule S M) x) =
        (SymmetricAlgebra.ι R M).baseChange (Localization S)
          ((LocalizedModule.isBaseChange S M).equiv.symm x))

end Semiring

section Ring

variable {R : Type u} [CommRing R]
variable (S : Submonoid R)
variable {M : Type v} [AddCommGroup M] [Module R M]

@[stacks 0C6F "(3), exterior algebra"]
#check ((LocalizedModule.isBaseChange S M).exteriorAlgebraEquiv.symm :
  ExteriorAlgebra (Localization S) (LocalizedModule S M) ≃ₐ[Localization S]
    Localization S ⊗[R] ExteriorAlgebra R M)

@[stacks 0C6F "(3), exterior algebra generator"]
#check (fun x : LocalizedModule S M ↦
  (LocalizedModule.isBaseChange S M).exteriorAlgebraEquiv_symm_apply_ι x :
    ∀ x : LocalizedModule S M,
      (LocalizedModule.isBaseChange S M).exteriorAlgebraEquiv.symm
          (ExteriorAlgebra.ι (Localization S) x) =
        (ExteriorAlgebra.ι R).baseChange (Localization S)
          ((LocalizedModule.isBaseChange S M).equiv.symm x))

end Ring
