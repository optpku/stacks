/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.DifferentialOperator.FiniteOrder
public import ReasLib.Algebra.Module.DifferentialOperator.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Formally Étale Base Change of Differential Operators

@stack 0H94
@stack 0H95

The public statement in this leaf is independent of a chosen presentation of
principal parts. The corresponding principal-parts comparison is owned by a
separate leaf; consumers here only need the universal extension property.
-/

@[expose] public section

universe u

open scoped TensorProduct

namespace LinearMap.IsDifferentialOperatorOfOrder.BaseChange.FormallyEtale

section FormallyEtale

variable {R S S' M N : Type u}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- An order-`k` differential operator has a unique order-preserving extension along a formally
étale scalar extension. -/
@[stacks 0H94]
theorem existsUnique_extension [Algebra.FormallyEtale S S']
    {D : M →ₗ[R] N} {k : ℕ} (hD : D.IsDifferentialOperatorOfOrder S k) :
    ∃! D' : S' ⊗[S] M →ₗ[R] S' ⊗[S] N, IsExtension D k D' := sorry

end FormallyEtale

end LinearMap.IsDifferentialOperatorOfOrder.BaseChange.FormallyEtale

namespace DifferentialOperator.FiniteOrderEndomorphisms

section FormallyEtale

variable {R S S' M : Type u}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

namespace BaseChange

/-- A finite-order target endomorphism extends a source endomorphism when the canonical
scalar-extension square commutes. -/
@[stacks 0H94]
def IsExtension
    (D : finiteOrderEndomorphisms (R := R) (S := S) (M := M))
    (D' : finiteOrderEndomorphisms (R := R) (S := S') (M := S' ⊗[S] M)) : Prop :=
  LinearMap.BaseChange.IsExtension (D : Module.End R M)
    (D' : Module.End R (S' ⊗[S] M))

/-- A ring hom is a finite-order base-change extension when it sends every source finite-order
endomorphism to an extending target endomorphism. -/
@[stacks 0H95]
def IsExtensionMap
    (F : finiteOrderEndomorphisms (R := R) (S := S) (M := M) →+*
      finiteOrderEndomorphisms (R := R) (S := S') (M := S' ⊗[S] M)) : Prop :=
  ∀ D : finiteOrderEndomorphisms (R := R) (S := S) (M := M),
    IsExtension D (F D)

/-- A finite-order base-change ring hom together with its pointwise extension property. -/
@[stacks 0H95]
structure Extension where
  /-- The ring homomorphism on finite-order differential endomorphisms. -/
  toRingHom : finiteOrderEndomorphisms (R := R) (S := S) (M := M) →+*
    finiteOrderEndomorphisms (R := R) (S := S') (M := S' ⊗[S] M)
  /-- The pointwise scalar-extension compatibility of `toRingHom`. -/
  isExtension : IsExtensionMap toRingHom

/-- The endomorphism-valued action associated to a finite-order base-change extension. -/
def Extension.toEnd
    (F : Extension (R := R) (S := S) (S' := S') (M := M)) :
    finiteOrderEndomorphisms (R := R) (S := S) (M := M) →+*
      Module.End R (S' ⊗[S] M) :=
  (finiteOrderEndomorphisms (R := R) (S := S') (M := S' ⊗[S] M)).subtype.comp F.toRingHom

/-- Evaluating `Extension.toEnd` is coercion of the finite-order target endomorphism. -/
@[simp]
theorem Extension.toEnd_apply
    (F : Extension (R := R) (S := S) (S' := S') (M := M))
    (D : finiteOrderEndomorphisms (R := R) (S := S) (M := M)) :
    F.toEnd D = (F.toRingHom D : Module.End R (S' ⊗[S] M)) := sorry

/-- The explicit module structure induced by a specified finite-order base-change extension.
It is not a global instance because `F` is genuine, non-inferable input data. -/
@[stacks 0H95, reducible]
def module (F : Extension (R := R) (S := S) (S' := S') (M := M)) :
    Module (finiteOrderEndomorphisms (R := R) (S := S) (M := M)) (S' ⊗[S] M) :=
  Module.compHom (S' ⊗[S] M) F.toEnd

end BaseChange

namespace FormallyEtale

/-- A finite-order endomorphism has a unique finite-order extension along a formally étale scalar
extension. -/
@[stacks 0H95]
theorem existsUnique_extension [Algebra.FormallyEtale S S']
    (D : finiteOrderEndomorphisms (R := R) (S := S) (M := M)) :
    ∃! D' : finiteOrderEndomorphisms (R := R) (S := S') (M := S' ⊗[S] M),
      BaseChange.IsExtension D D' := sorry

/-- Raw-map form of `existsUnique_extension`; the extension remains bundled so that its
finite-order content is not carried as a repeated proof hypothesis. -/
@[stacks 0H95]
theorem existsUnique_extension_of_mem [Algebra.FormallyEtale S S']
    (D : Module.End R M)
    (hD : D ∈ finiteOrderEndomorphisms (R := R) (S := S) (M := M)) :
    ∃! D' : finiteOrderEndomorphisms (R := R) (S := S') (M := S' ⊗[S] M),
      LinearMap.BaseChange.IsExtension D (D' : Module.End R (S' ⊗[S] M)) := sorry

/-- Formally étale scalar extension induces the unique ring homomorphism on finite-order
differential endomorphisms whose maps extend the original endomorphisms. -/
@[stacks 0H95]
theorem existsUnique_ringHom [Algebra.FormallyEtale S S'] :
    ∃! F : finiteOrderEndomorphisms (R := R) (S := S) (M := M) →+*
      finiteOrderEndomorphisms (R := R) (S := S') (M := S' ⊗[S] M),
      BaseChange.IsExtensionMap F := sorry

/-- A finite-order base-change ring hom carries scalar multiplication by `s : S` to scalar
multiplication by `algebraMap S S' s`. -/
@[stacks 0H95]
theorem ringHom_apply_smul [Algebra.FormallyEtale S S']
    (F : BaseChange.Extension (R := R) (S := S) (S' := S') (M := M))
    (s : S) :
    (F.toRingHom (smulRingHom (R := R) (S := S) (M := M) s) :
      Module.End R (S' ⊗[S] M)) =
      DistribSMul.toLinearMap R (S' ⊗[S] M) (algebraMap S S' s) := sorry

end FormallyEtale

end FormallyEtale

end DifferentialOperator.FiniteOrderEndomorphisms
