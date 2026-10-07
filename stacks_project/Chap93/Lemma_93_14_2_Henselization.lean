module

public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.RingTheory.Henselian.Pair.BaseChange
public import ReasLib.RingTheory.Henselian.Pair.Category
public import stacks_project.Chap93.Lemma_93_12_4_Exal

/-!
# Pair henselization of first-order algebra extensions

Henselizing a square-zero extension `0 → N → C → B → 0` along the inverse image
of `J ⊂ B` yields an extension of `henselizationRing (pairOfIdeal J)` by
`N ⊗[B] henselizationRing (pairOfIdeal J)`. On Ext¹ classes this is
`Algebra.Exal.henselization`.
-/

@[expose] public section

noncomputable section

universe u

open Algebra Algebra.Generators Algebra.Extension
open CategoryTheory
open RingPairCat
open scoped TensorProduct

namespace Algebra.Exal

variable (B N : Type u) [CommRing B] [AddCommGroup N] [Module B N]

/-- `N ⊗[B] B^h` carries the `B^h`-action transported from `B^h ⊗[B] N`. -/
instance instModule_tensor_henselizationRing (J : Ideal B)
    [henselianPairInclusion.IsRightAdjoint] :
    Module (henselizationRing (pairOfIdeal J) : Type u)
      (N ⊗[B] (henselizationRing (pairOfIdeal J) : Type u)) :=
  (_root_.TensorProduct.comm B N
      (henselizationRing (pairOfIdeal J) : Type u)).toAddEquiv.module
    (henselizationRing (pairOfIdeal J) : Type u)

end Algebra.Exal

namespace Algebra.SquareZeroAlgExtension

variable {A B N : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module B N]

/-- Inverse image of `J` along the projection of a square-zero extension. -/
def comapIdeal (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
    @Ideal e.carrier e.commRing.toSemiring :=
  -- Local instance justification (proof-local temporary data): unpack bundled `commRing` so `Ideal.comap` on `e.toB` can elaborate.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack bundled `algebra` so `e.toB` elaborates as an algebra homomorphism.
  letI := e.algebra
  Ideal.comap e.toB.toRingHom J

/-- Membership in `comapIdeal e J` is membership of the image in `J`. -/
theorem mem_comapIdeal (e : SquareZeroAlgExtension A B N) (J : Ideal B)
    {x : e.carrier} : x ∈ comapIdeal e J ↔ e.toB x ∈ J := sorry

/-- `comapIdeal` is the preimage of `J` along the projection. -/
theorem comapIdeal_eq_comap (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
    (comapIdeal e J : Set e.carrier) = e.toB ⁻¹' (J : Set B) := sorry

/-- Pair morphism `(C, J_C) ⟶ (B, J)` induced by a square-zero projection. -/
def pairHom (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
    @pairOfIdeal e.carrier e.commRing (comapIdeal e J) ⟶ pairOfIdeal J :=
  -- Local instance justification (proof-local temporary data): unpack bundled `commRing` so `pairOfIdeal` on `e.carrier` can elaborate.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack bundled `algebra` so `e.toB` elaborates as an algebra homomorphism.
  letI := e.algebra
  let f := e.toB.toRingHom
  let I := comapIdeal e J
  InducedCategory.homMk <|
    Arrow.homMk' (CommRingCat.ofHom f)
      (CommRingCat.ofHom (Ideal.quotientMap J f (le_rfl : I ≤ Ideal.comap f J)))
      (pairOfIdeal_hom_square_of_ringHom I J f le_rfl)

/-- The underlying ring homomorphism of `pairHom` is the square-zero projection. -/
theorem pairHom_ringHom (e : SquareZeroAlgExtension A B N) (J : Ideal B)
    (x : e.carrier) : ringHom (pairHom e J) x = e.toB x := sorry

/-- Henselizing a geometric representative along the inverse image of `J`. -/
def henselization [henselianPairInclusion.IsRightAdjoint]
    (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
    SquareZeroAlgExtension A (henselizationRing (pairOfIdeal J) : Type u)
      (N ⊗[B] (henselizationRing (pairOfIdeal J) : Type u)) :=
  -- Local instance justification (proof-local temporary data): unpack bundled `commRing` so pair henselization of `e.carrier` can elaborate.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack bundled `algebra` so the composite `A`-algebra on the henselization of `e.carrier` can elaborate.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack bundled `isSquareZero` so kernel identifications of `e.toB` can elaborate.
  letI := e.isSquareZero
  let Bh := (henselizationRing (pairOfIdeal J) : Type u)
  let Ch := (henselizationRing (pairOfIdeal (comapIdeal e J)) : Type u)
  let toB' : Ch →ₐ[A] Bh :=
    { toRingHom := henselizationRingMap (pairHom e J), commutes' := sorry }
  -- Local instance justification (proof-local temporary data): the henselized projection is square-zero, needed to assemble `of`.
  letI : toB'.toRingHom.IsSquareZeroExtension := ⟨sorry, sorry⟩
  -- Local instance justification (proof-local temporary data): restrict scalars along `B → B^h` so the unit map on cotangents lifts across `N ⊗[B] B^h`.
  letI : Module B (Ideal.Cotangent (RingHom.ker toB'.toRingHom)) :=
    Module.compHom _ (algebraMap B Bh)
  -- Local instance justification (proof-local temporary data): scalar tower for `liftBaseChange` of the unit map on cotangents.
  letI : IsScalarTower B Bh (Ideal.Cotangent (RingHom.ker toB'.toRingHom)) :=
    ⟨fun _ _ _ ↦ sorry⟩
  let cotUnit :
      Ideal.Cotangent (RingHom.ker e.toB.toRingHom) →ₗ[B]
        Ideal.Cotangent (RingHom.ker toB'.toRingHom) :=
    { toFun := fun y ↦
        let yKer :=
          (LinearEquiv.ofBijective (Ideal.toCotangent (RingHom.ker e.toB.toRingHom))
            ⟨sorry, sorry⟩).symm y
        Ideal.toCotangent (RingHom.ker toB'.toRingHom)
          ⟨toHenselization (pairOfIdeal (comapIdeal e J)) yKer.1, sorry⟩
      map_add' := sorry
      map_smul' := sorry }
  let tensUnit :
      Ideal.Cotangent (RingHom.ker e.toB.toRingHom) ⊗[B] Bh →ₗ[B]
        Ideal.Cotangent (RingHom.ker toB'.toRingHom) :=
    { toFun := fun t ↦
        cotUnit.liftBaseChange Bh
          (_root_.TensorProduct.comm B
            (Ideal.Cotangent (RingHom.ker e.toB.toRingHom)) Bh t)
      map_add' := sorry
      map_smul' := sorry }
  let mapKer :
      Ideal.Cotangent (RingHom.ker e.toB.toRingHom) ⊗[B] Bh →ₗ[B] N ⊗[B] Bh :=
    _root_.TensorProduct.map e.kernelEquiv.toLinearMap (LinearMap.id : Bh →ₗ[B] Bh)
  let kerMap :
      Ideal.Cotangent (RingHom.ker toB'.toRingHom) →ₗ[Bh] N ⊗[B] Bh :=
    { toFun := fun x ↦
        mapKer ((LinearEquiv.ofBijective tensUnit ⟨sorry, sorry⟩).symm x)
      map_add' := sorry
      map_smul' := sorry }
  of toB' (LinearEquiv.ofBijective kerMap ⟨sorry, sorry⟩)

/-- The middle ring of `henselization` is the pair henselization of `(C, J_C)`. -/
theorem henselization_carrier [henselianPairInclusion.IsRightAdjoint]
    (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
    (e.henselization J).carrier =
      (henselizationRing (@pairOfIdeal e.carrier e.commRing (comapIdeal e J)) : Type u) :=
  sorry

end Algebra.SquareZeroAlgExtension

namespace Algebra.Exal

variable (A B N : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module B N]

/-- Pair henselization of first-order extensions, on Ext¹ classes. -/
def henselization [henselianPairInclusion.IsRightAdjoint] (J : Ideal B) :
    Exal A B N →
      Exal A (henselizationRing (pairOfIdeal J) : Type u)
        (N ⊗[B] (henselizationRing (pairOfIdeal J) : Type u)) :=
  fun x ↦
    Quotient.liftOn x
      (fun f ↦ SquareZeroAlgExtension.toClass
        ((SquareZeroAlgExtension.ofHom f).henselization J))
      (fun _ _ _ ↦ sorry)

/-- Henselizing the class of a cotangent map is the class of the henselized pushout. -/
theorem henselization_mk [henselianPairInclusion.IsRightAdjoint] (J : Ideal B)
    (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    henselization A B N J (mk A B N f) =
      SquareZeroAlgExtension.toClass
        ((SquareZeroAlgExtension.ofHom f).henselization J) := sorry

/-- Unfolding of `Exal.henselization` on a quotient representative. -/
theorem henselization_apply [henselianPairInclusion.IsRightAdjoint] (J : Ideal B)
    (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    henselization A B N J (Quotient.mk _ f) = henselization A B N J (mk A B N f) :=
  sorry

end Algebra.Exal
