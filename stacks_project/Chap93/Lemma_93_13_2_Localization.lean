/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Localization.Module
public import stacks_project.Chap93.Lemma_93_12_4_Exal

/-!
# Localization of first-order algebra extensions

Localizing a square-zero extension `0 → N → C → B → 0` along the inverse image
of a multiplicative subset `S ⊆ B` yields an extension of `Localization S` by
`LocalizedModule S N`. On Ext¹ classes this is `Algebra.Exal.localize`.
-/

@[expose] public section

noncomputable section

universe u

open Algebra

namespace Algebra.SquareZeroAlgExtension

variable {A B N : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module B N]

/-- Inverse image of a multiplicative subset along the projection of a
square-zero extension. -/
abbrev localizationSubmonoid (e : SquareZeroAlgExtension A B N) (S : Submonoid B) :
    @Submonoid e.carrier e.commRing.toMonoid.toMulOneClass :=
  -- Local instance justification (proof-local temporary data): unpack bundled `commRing` so `Submonoid.comap` on `e.toB` can elaborate.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack bundled `algebra` so `e.toB` elaborates as an algebra homomorphism.
  letI := e.algebra
  S.comap e.toB.toRingHom

/-- `localizationSubmonoid` is the preimage of `S` along the projection. -/
theorem localizationSubmonoid_eq_comap (e : SquareZeroAlgExtension A B N)
    (S : Submonoid B) :
    (localizationSubmonoid e S : Set e.carrier) = e.toB ⁻¹' (S : Set B) := sorry

/-- Membership in `localizationSubmonoid e S` is membership of the image in `S`. -/
theorem mem_localizationSubmonoid (e : SquareZeroAlgExtension A B N) (S : Submonoid B)
    {x : e.carrier} :
    x ∈ localizationSubmonoid e S ↔ e.toB x ∈ S := sorry

/-- Localizing a geometric representative along the inverse image of `S`. -/
def localize (e : SquareZeroAlgExtension A B N) (S : Submonoid B) :
    SquareZeroAlgExtension A (Localization S) (LocalizedModule S N) :=
  -- Local instance justification (proof-local temporary data): unpack bundled `commRing` so `Localization` of `e.carrier` can elaborate.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack bundled `algebra` so `Localization` inherits an `A`-algebra structure.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack bundled `isSquareZero` so kernel identifications of `e.toB` can elaborate.
  letI := e.isSquareZero
  let S_C : Submonoid e.carrier := S.comap e.toB.toRingHom
  let toBRing :=
    (IsLocalization.map (Localization S) e.toB.toRingHom
      (le_rfl : S_C ≤ S.comap e.toB.toRingHom) :
      Localization S_C →+* Localization S)
  let toB' : Localization S_C →ₐ[A] Localization S :=
    { toRingHom := toBRing, commutes' := sorry }
  -- Local instance justification (proof-local temporary data): the localized projection is square-zero, needed to assemble `of`.
  letI : toB'.toRingHom.IsSquareZeroExtension := ⟨sorry, sorry⟩
  let kerIncl : RingHom.ker e.toB.toRingHom →ₗ[e.carrier] e.carrier :=
    Submodule.subtype (RingHom.ker e.toB.toRingHom)
  let localizedKerIncl :
      LocalizedModule S_C (RingHom.ker e.toB.toRingHom) →
        RingHom.ker toB'.toRingHom :=
    fun z ↦
      ⟨LocalizedModule.liftOn z
        (fun p ↦ Localization.mk (kerIncl p.1) p.2)
        (fun _ _ _ ↦ sorry), sorry⟩
  let localizedKerEquiv := Equiv.ofBijective localizedKerIncl ⟨sorry, sorry⟩
  of toB'
    (LinearEquiv.ofBijective
      { toFun := fun x : Ideal.Cotangent (RingHom.ker toB'.toRingHom) ↦
          let xKer :=
            (LinearEquiv.ofBijective
              (Ideal.toCotangent (RingHom.ker toB'.toRingHom)) ⟨sorry, sorry⟩).symm x
          let z := localizedKerEquiv.symm xKer
          let zCot :=
            LocalizedModule.liftOn z
              (fun p ↦
                LocalizedModule.mk
                  (Ideal.toCotangent (RingHom.ker e.toB.toRingHom) p.1)
                  ⟨e.toB p.2, p.2.property⟩)
              (fun _ _ _ ↦ sorry)
          LocalizedModule.map S e.kernelEquiv.toLinearMap zCot
        map_add' := sorry
        map_smul' := sorry }
      ⟨sorry, sorry⟩)

end Algebra.SquareZeroAlgExtension

namespace Algebra.Exal

variable (A B N : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module B N]

/-- Localization of first-order extensions, on Ext¹ classes. -/
def localize (S : Submonoid B) :
    Exal A B N → Exal A (Localization S) (LocalizedModule S N) :=
  fun x ↦
    Quotient.liftOn x
      (fun f ↦ SquareZeroAlgExtension.toClass
        ((SquareZeroAlgExtension.ofHom f).localize S))
      (fun _ _ _ ↦ sorry)

/-- Localizing the class of a cotangent map is the class of the localized pushout. -/
theorem localize_mk (S : Submonoid B)
    (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    localize A B N S (mk A B N f) =
      SquareZeroAlgExtension.toClass
        ((SquareZeroAlgExtension.ofHom f).localize S) := sorry

/-- Unfolding of `Exal.localize` on a quotient representative. -/
theorem localize_apply (S : Submonoid B)
    (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    localize A B N S (Quotient.mk _ f) =
      SquareZeroAlgExtension.toClass
        ((SquareZeroAlgExtension.ofHom f).localize S) := sorry

/-- Localization of Ext¹ classes sends a geometric representative to its localization. -/
theorem localize_toClass (S : Submonoid B)
    (e : SquareZeroAlgExtension A B N) :
    localize A B N S (SquareZeroAlgExtension.toClass e) =
      SquareZeroAlgExtension.toClass (e.localize S) := sorry

end Algebra.Exal
