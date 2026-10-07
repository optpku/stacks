module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.FiniteType
public import ReasLib.RingTheory.AdicCompletion.Exactness.ShortComplex
public import ReasLib.RingTheory.AdicCompletion.FilteredAdditive
public import ReasLib.RingTheory.AdicCompletion.Map
public import stacks_project.Chap93.Lemma_93_12_4_Exal

/-!
# J-adic completion of first-order algebra extensions

Completing a square-zero extension `0 → N → C → B → 0` along the inverse image
of `J ⊂ B` yields an extension of `AdicCompletion J B` by `AdicCompletion J N`.
On Ext¹ classes this is `Algebra.Exal.adicCompletion`.
-/

@[expose] public section

noncomputable section

universe u

open Algebra Algebra.Generators Algebra.Extension
open RingHom RingHom.AdicContinuous
open AdicCompletion
open CategoryTheory

namespace Algebra.SquareZeroAlgExtension

variable {A B N : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module B N]

/-- Inverse image of `J` along the projection of a square-zero extension. -/
def adicCompletionIdeal (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
    @Ideal e.carrier e.commRing.toSemiring :=
  -- Local instance justification (proof-local temporary data): unpack bundled `commRing` so `Ideal.comap` on `e.toB` can elaborate.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack bundled `algebra` so `e.toB` elaborates as an algebra homomorphism.
  letI := e.algebra
  Ideal.comap e.toB.toRingHom J

/-- `adicCompletionIdeal` is the preimage of `J` along the projection. -/
theorem adicCompletionIdeal_eq_comap (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
    (adicCompletionIdeal e J : Set e.carrier) = e.toB ⁻¹' (J : Set B) := sorry

/-- Membership in `adicCompletionIdeal e J` is membership of the image in `J`. -/
theorem mem_adicCompletionIdeal (e : SquareZeroAlgExtension A B N) (J : Ideal B)
    {x : e.carrier} :
    x ∈ adicCompletionIdeal e J ↔ e.toB x ∈ J := sorry

/-- Completing a geometric representative along the inverse image of `J`. -/
def adicCompletion [IsNoetherianRing B] [Module.Finite B N]
    (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
    SquareZeroAlgExtension A (AdicCompletion J B) (AdicCompletion J N) :=
  -- Local instance justification (proof-local temporary data): unpack bundled `commRing` so `AdicCompletion` of `e.carrier` can elaborate.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack bundled `algebra` so `AdicCompletion` inherits an `A`-algebra structure.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack bundled `isSquareZero` so kernel identifications of `e.toB` can elaborate.
  letI := e.isSquareZero
  let I : Ideal e.carrier := Ideal.comap e.toB.toRingHom J
  let hcont : e.toB.toRingHom.AdicContinuous I J :=
    AdicContinuous.of e.toB.toRingHom I J 1 sorry
  let toB' : AdicCompletion I e.carrier →ₐ[A] AdicCompletion J B :=
    { toRingHom := hcont.completionMap, commutes' := sorry }
  -- Local instance justification (proof-local temporary data): the completed projection is square-zero, needed to assemble `of`.
  letI : toB'.toRingHom.IsSquareZeroExtension := ⟨sorry, sorry⟩
  -- Local instance justification (proof-local temporary data): view `B` as an `e.carrier`-module via the square-zero projection so the kernel sequence is a short complex of modules.
  letI : Module e.carrier B := Module.compHom B e.toB.toRingHom
  let kerIncl : RingHom.ker e.toB.toRingHom →ₗ[e.carrier] e.carrier :=
    Submodule.subtype (RingHom.ker e.toB.toRingHom)
  let toBLinear : e.carrier →ₗ[e.carrier] B :=
    { toFun := e.toB, map_add' := map_add e.toB.toRingHom, map_smul' := sorry }
  let S := ShortComplex.moduleCatMk kerIncl toBLinear sorry
  let S' := AdicCompletion.mapShortComplex I S
  let completedKerIncl :
      AdicCompletion I (RingHom.ker e.toB.toRingHom) →
        RingHom.ker toB'.toRingHom :=
    fun z ↦ ⟨S'.f.hom z, sorry⟩
  let completedKerEquiv := Equiv.ofBijective completedKerIncl ⟨sorry, sorry⟩
  of toB'
    (LinearEquiv.ofBijective
      { toFun := fun x : Ideal.Cotangent (RingHom.ker toB'.toRingHom) ↦
          let xKer :=
            (LinearEquiv.ofBijective
              (Ideal.toCotangent (RingHom.ker toB'.toRingHom)) ⟨sorry, sorry⟩).symm x
          let z := completedKerEquiv.symm xKer
          let zCot :=
            AdicCompletion.map I (Ideal.toCotangent (RingHom.ker e.toB.toRingHom)) z
          let zCotJ :=
            FilteredAdditiveCompletion.map I J
              (AddMonoidHom.id (Ideal.Cotangent (RingHom.ker e.toB.toRingHom))) sorry zCot
          AdicCompletion.map J e.kernelEquiv.toLinearMap zCotJ
        map_add' := sorry
        map_smul' := sorry }
      ⟨sorry, sorry⟩)

end Algebra.SquareZeroAlgExtension

namespace Algebra.Exal

variable (A B N : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module B N]

/-- J-adic completion of first-order extensions, on Ext¹ classes. -/
def adicCompletion [IsNoetherianRing B] [Module.Finite B N] (J : Ideal B) :
    Exal A B N → Exal A (AdicCompletion J B) (AdicCompletion J N) :=
  fun x ↦
    Quotient.liftOn x
      (fun f ↦ SquareZeroAlgExtension.toClass
        ((SquareZeroAlgExtension.ofHom f).adicCompletion J))
      (fun _ _ _ ↦ sorry)

/-- Completing the class of a cotangent map is the class of the completed pushout. -/
theorem adicCompletion_mk [IsNoetherianRing B] [Module.Finite B N] (J : Ideal B)
    (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    adicCompletion A B N J (mk A B N f) =
      SquareZeroAlgExtension.toClass
        ((SquareZeroAlgExtension.ofHom f).adicCompletion J) := sorry

/-- Unfolding of `Exal.adicCompletion` on a quotient representative. -/
theorem adicCompletion_apply [IsNoetherianRing B] [Module.Finite B N] (J : Ideal B)
    (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    adicCompletion A B N J (Quotient.mk _ f) =
      adicCompletion A B N J (mk A B N f) := sorry

end Algebra.Exal
