/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensor products of residue fields

This file defines the tensor products and comparison maps associated to two
prime ideals with specified embeddings of a common field into their residue
fields.
-/

@[expose] public section

universe u

open scoped TensorProduct

namespace Ideal.ResidueField

variable {A k : Type u} [CommRing A] [Field k]

/-- The tensor product `κ(I) ⊗[k] κ(J)` of residue fields along given embeddings of `k`. -/
abbrev tensor {I J : Ideal A} [I.IsPrime] [J.IsPrime]
    (ιI : k →+* I.ResidueField) (ιJ : k →+* J.ResidueField) : Type u :=
  @TensorProduct k _ I.ResidueField J.ResidueField _ _ ιI.toAlgebra.toModule ιJ.toAlgebra.toModule

/-- The induced ring map `A ⊗[ℤ] A →+* κ(I) ⊗[k] κ(J)` from the two residue-field maps. -/
noncomputable def tensorHomOfAlgebra {I J : Ideal A} [I.IsPrime] [J.IsPrime]
    [Algebra k I.ResidueField] [Algebra k J.ResidueField] :
    A ⊗[ℤ] A →+* I.ResidueField ⊗[k] J.ResidueField :=
  @AlgHom.toRingHom ℤ (A ⊗[ℤ] A) (I.ResidueField ⊗[k] J.ResidueField)
    _ _ _ _ (Ring.toIntAlgebra (I.ResidueField ⊗[k] J.ResidueField))
    (@Algebra.TensorProduct.productMap ℤ (I.ResidueField ⊗[k] J.ResidueField) A A
      inferInstance inferInstance inferInstance inferInstance
      (Ring.toIntAlgebra A) (Ring.toIntAlgebra A)
      (Ring.toIntAlgebra (I.ResidueField ⊗[k] J.ResidueField))
      ((Algebra.TensorProduct.includeLeftRingHom :
          I.ResidueField →+* I.ResidueField ⊗[k] J.ResidueField).comp
        (algebraMap A I.ResidueField)).toIntAlgHom
      ((Algebra.TensorProduct.includeRight :
          J.ResidueField →ₐ[k] I.ResidueField ⊗[k] J.ResidueField).toRingHom.comp
        (algebraMap A J.ResidueField)).toIntAlgHom)

/-- Evaluation of `tensorHomOfAlgebra` on elementary tensors. -/
theorem tensorHomOfAlgebra_tmul {I J : Ideal A} [I.IsPrime] [J.IsPrime]
    [Algebra k I.ResidueField] [Algebra k J.ResidueField] (a b : A) :
    tensorHomOfAlgebra (a ⊗ₜ[ℤ] b) =
      algebraMap A I.ResidueField a ⊗ₜ[k] algebraMap A J.ResidueField b :=
  sorry

/-- The induced ring map `A ⊗[ℤ] A →+* κ(I) ⊗[k] κ(J)` for specified embeddings. -/
noncomputable def tensorHom {I J : Ideal A} [I.IsPrime] [J.IsPrime]
    (ιI : k →+* I.ResidueField) (ιJ : k →+* J.ResidueField) :
    A ⊗[ℤ] A →+* tensor ιI ιJ :=
  @tensorHomOfAlgebra A k _ _ I J _ _ ιI.toAlgebra ιJ.toAlgebra

/-- The elementary tensor of residue-field elements for specified embeddings. -/
noncomputable def tensorTmul {I J : Ideal A} [I.IsPrime] [J.IsPrime]
    (ιI : k →+* I.ResidueField) (ιJ : k →+* J.ResidueField)
    (a : I.ResidueField) (b : J.ResidueField) : tensor ιI ιJ :=
  @TensorProduct.tmul k _ I.ResidueField J.ResidueField _ _
    ιI.toAlgebra.toModule ιJ.toAlgebra.toModule a b

/-- Evaluation of `tensorHom` on elementary tensors. -/
theorem tensorHom_tmul {I J : Ideal A} [I.IsPrime] [J.IsPrime]
    (ιI : k →+* I.ResidueField) (ιJ : k →+* J.ResidueField) (a b : A) :
    tensorHom ιI ιJ (a ⊗ₜ[ℤ] b) =
      tensorTmul ιI ιJ (algebraMap A I.ResidueField a) (algebraMap A J.ResidueField b) :=
  sorry

end Ideal.ResidueField
