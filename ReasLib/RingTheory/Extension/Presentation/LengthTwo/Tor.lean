/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Exact.Basic
public import ReasLib.RingTheory.Extension.Presentation.LengthTwo.Terms
public import ReasLib.RingTheory.Ideal.Tensor.MultiplicationKernel

/-!
# Tensor kernels of length-two polynomial presentations

The exterior, conormal, and degeneracy summands give explicit tensor maps.
The difference of the two faces has a canonical module cokernel and a
right-exact conormal exterior comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Algebra Ideal MvPolynomial
open scoped TensorProduct

noncomputable section

universe u

namespace Algebra.Presentation.LengthTwo

variable {A B ι σ : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The augmentation of the degree-one polynomial ring obtained from the zero face. -/
def term1AlgHom (P : Presentation A B ι σ) : term1 P →ₐ[A] B :=
  (aeval P.val).comp (faceZero P)

/-- The degree-one augmentation is surjective. -/
theorem term1AlgHom_surjective (P : Presentation A B ι σ) :
    Function.Surjective (term1AlgHom P) := sorry

/-- The ideal of the degree-one augmentation. -/
def term1Ker (P : Presentation A B ι σ) : Ideal (term1 P) :=
  RingHom.ker (term1AlgHom P).toRingHom

/-- The degree-one multiplication kernel as a module over the presented algebra. -/
def term1MulKerModuleCat (P : Presentation A B ι σ) : ModuleCat.{u} B :=
  mulKerModuleCat (term1AlgHom P).toRingHom (term1AlgHom_surjective P)

/-- The degree-zero multiplication kernel as a module over the presented algebra. -/
def term0MulKerModuleCat (P : Presentation A B ι σ) : ModuleCat.{u} B :=
  (ModuleCat.restrictScalars P.quotientEquiv.symm.toRingHom).obj
    (mulKerQuotientModuleCat P.ker)

/-- The conormal module with scalars transported along the presentation quotient equivalence. -/
def kerCotangentModuleCat (P : Presentation A B ι σ) : ModuleCat.{u} B :=
  (ModuleCat.restrictScalars P.quotientEquiv.symm.toRingHom).obj
    (ModuleCat.of (P.Ring ⧸ P.ker) P.ker.Cotangent)

/-- Each new polynomial generator belongs to the degree-one augmentation ideal. -/
theorem x_mem_term1Ker (P : Presentation A B ι σ) (t : σ) :
    x P t ∈ term1Ker P := sorry

/-- A new polynomial generator as an element of the augmentation ideal. -/
def xKer (P : Presentation A B ι σ) (t : σ) : term1Ker P :=
  ⟨x P t, x_mem_term1Ker P t⟩

/-- The underlying polynomial of the kernel generator is the designated indeterminate. -/
theorem xKer_coe (P : Presentation A B ι σ) (t : σ) :
    (xKer P t : term1 P) = x P t := rfl

/-- The degeneracy preserves augmentation ideals. -/
theorem degeneracyZero_mem_term1Ker (P : Presentation A B ι σ) {f : P.Ring}
    (hf : f ∈ P.ker) : degeneracyZero P f ∈ term1Ker P := sorry

/-- The additive restriction of the degeneracy to augmentation ideals. -/
def degeneracyZero_mapKer (P : Presentation A B ι σ) : P.ker →+ term1Ker P :=
  AddMonoidHom.codRestrict
    ((degeneracyZero P).toRingHom.toAddMonoidHom.comp
      (Submodule.subtype P.ker).toAddMonoidHom)
    (term1Ker P) (fun f => degeneracyZero_mem_term1Ker P f.2)

/-- The zero face preserves augmentation ideals. -/
theorem faceZero_mem_ker (P : Presentation A B ι σ) {p : term1 P}
    (hp : p ∈ term1Ker P) : faceZero P p ∈ P.ker := sorry

/-- The one face preserves augmentation ideals. -/
theorem faceOne_mem_ker (P : Presentation A B ι σ) {p : term1 P}
    (hp : p ∈ term1Ker P) : faceOne P p ∈ P.ker := sorry

/-- A defining relation as an element of the presentation ideal. -/
def relationKer (P : Presentation A B ι σ) (t : σ) : P.ker :=
  ⟨P.relation t, P.relation_mem_ker t⟩

/-- Weighted alternating generator tensors are additive in each family. -/
theorem wedgeInclAlternating_map_update_add (P : Presentation A B ι σ)
    [DecidableEq (Fin 2)] (v : Fin 2 → σ →₀ B) (i : Fin 2) (a b : σ →₀ B) :
    let pair := fun v : Fin 2 → σ →₀ B =>
      (v 0).sum fun t a => (v 1).sum fun t' b =>
        HSMul.hSMul (β := term1MulKerModuleCat P) (γ := term1MulKerModuleCat P)
          (a * b) (alternTmul (xKer P t) (xKer P t'))
    pair (Function.update v i (a + b)) =
      pair (Function.update v i a) + pair (Function.update v i b) := sorry

/-- Weighted alternating generator tensors are linear over the presented algebra. -/
theorem wedgeInclAlternating_map_update_smul (P : Presentation A B ι σ)
    [DecidableEq (Fin 2)] (v : Fin 2 → σ →₀ B) (i : Fin 2) (r : B) (a : σ →₀ B) :
    let pair := fun v : Fin 2 → σ →₀ B =>
      (v 0).sum fun t a => (v 1).sum fun t' b =>
        HSMul.hSMul (β := term1MulKerModuleCat P) (γ := term1MulKerModuleCat P)
          (a * b) (alternTmul (xKer P t) (xKer P t'))
    pair (Function.update v i (r • a)) = r • pair (Function.update v i a) := sorry

/-- Weighted alternating generator tensors vanish on repeated arguments. -/
theorem wedgeInclAlternating_map_eq_zero_of_eq (P : Presentation A B ι σ)
    (v : Fin 2 → σ →₀ B) (i j : Fin 2) (h : v i = v j) (hij : i ≠ j) :
    (v 0).sum (fun t a => (v 1).sum fun t' b =>
      HSMul.hSMul (β := term1MulKerModuleCat P) (γ := term1MulKerModuleCat P)
        (a * b) (alternTmul (xKer P t) (xKer P t'))) = 0 := sorry

/-- The alternating sum of tensors of new generators, weighted by two finitely supported families. -/
def wedgeInclAlternating (P : Presentation A B ι σ) :
    (σ →₀ B) [⋀^Fin 2]→ₗ[B] term1MulKerModuleCat P where
  toFun v := (v 0).sum fun t a => (v 1).sum fun t' b =>
    HSMul.hSMul (β := term1MulKerModuleCat P) (γ := term1MulKerModuleCat P)
      (a * b) (alternTmul (xKer P t) (xKer P t'))
  map_update_add' := wedgeInclAlternating_map_update_add P
  map_update_smul' := wedgeInclAlternating_map_update_smul P
  map_eq_zero_of_eq' := wedgeInclAlternating_map_eq_zero_of_eq P

/-- The linear exterior summand map into the degree-one multiplication kernel. -/
def wedgeIncl (P : Presentation A B ι σ) :
    ⋀[B]^2 (σ →₀ B) →ₗ[B] term1MulKerModuleCat P :=
  exteriorPower.alternatingMapLinearEquiv (wedgeInclAlternating P)

/-- The exterior summand sends an ordered basis wedge to its ordered alternating tensor. -/
theorem wedgeIncl_apply (P : Presentation A B ι σ) (t t' : σ) :
    wedgeIncl P (exteriorPower.ιMulti B 2 fun i =>
      Finsupp.single (if i = 0 then t else t') (1 : B)) =
      alternTmul (xKer P t) (xKer P t') := sorry

/-- The mixed alternating tensor is additive in its degree-zero ideal argument. -/
theorem mixedInclSingle_map_add (P : Presentation A B ι σ) (t : σ) (f g : P.ker) :
    alternTmul (xKer P t) (degeneracyZero_mapKer P (f + g)) =
      alternTmul (xKer P t) (degeneracyZero_mapKer P f) +
        alternTmul (xKer P t) (degeneracyZero_mapKer P g) := sorry

/-- The mixed tensor of a new generator and a degenerate ideal element. -/
def mixedInclSingle (P : Presentation A B ι σ) (t : σ) :
    P.ker →+ term1MulKerModuleCat P :=
  AddMonoidHom.mk' (fun f => alternTmul (xKer P t) (degeneracyZero_mapKer P f))
    (mixedInclSingle_map_add P t)

/-- The mixed tensor vanishes on the square of the presentation ideal. -/
theorem mixedInclSingle_vanishes_sq (P : Presentation A B ι σ) (t : σ) (f : P.ker)
    (hf : (f : P.Ring) ∈ P.ker ^ 2) : mixedInclSingle P t f = 0 := sorry

/-- The mixed tensor map descended to the conormal module. -/
def mixedInclSingleCotangent (P : Presentation A B ι σ) (t : σ) :
    kerCotangentModuleCat P →+ term1MulKerModuleCat P :=
  QuotientAddGroup.lift (P.ker • (⊤ : Submodule P.Ring P.ker)).toAddSubgroup
    (mixedInclSingle P t) (by
      intro f hf
      apply mixedInclSingle_vanishes_sq P t f
      apply (P.ker.toCotangent_eq_zero f).mp
      exact (Submodule.Quotient.mk_eq_zero _).2 hf)

/-- The sum of the mixed conormal inclusions indexed by the new generators. -/
def mixedIncl (P : Presentation A B ι σ) :
    (σ →₀ kerCotangentModuleCat P) →+ term1MulKerModuleCat P :=
  Finsupp.liftAddHom (mixedInclSingleCotangent P)

/-- The mixed conormal inclusion has the specified alternating tensor on every representative. -/
theorem mixedIncl_apply (P : Presentation A B ι σ) (t : σ) (f : P.ker) :
    mixedIncl P (Finsupp.single t (P.ker.toCotangent f)) =
      alternTmul (xKer P t) (degeneracyZero_mapKer P f) := sorry

/-- Representatives in the square of the presentation ideal have zero mixed image. -/
theorem mixedIncl_apply_eq_zero_of_mem_sq (P : Presentation A B ι σ) (t : σ) (f : P.ker)
    (hf : (f : P.Ring) ∈ P.ker ^ 2) :
    mixedIncl P (Finsupp.single t (P.ker.toCotangent f)) = 0 := sorry

/-- The multiplication-kernel map induced by the polynomial degeneracy. -/
def degeneracyIncl (P : Presentation A B ι σ) :
    term0MulKerModuleCat P →+ term1MulKerModuleCat P :=
  mulKerMap (degeneracyZero P).toRingHom (fun _ hf => degeneracyZero_mem_term1Ker P hf)

/-- The product of exterior, conormal, and degree-zero tensor-kernel factors. -/
def torTwoTerm1SourceModuleCat (P : Presentation A B ι σ) : ModuleCat.{u} B :=
  ModuleCat.of B ((⋀[B]^2 (σ →₀ B)) ×
    (σ →₀ kerCotangentModuleCat P) × term0MulKerModuleCat P)

/-- The sum of the exterior, mixed, and degeneracy tensor maps. -/
def torTwoTerm1Coprod (P : Presentation A B ι σ) :
    torTwoTerm1SourceModuleCat P →+ term1MulKerModuleCat P :=
  (wedgeIncl P).toAddMonoidHom.coprod ((mixedIncl P).coprod (degeneracyIncl P))

/-- The sum of the three tensor inclusions is linear over the presented algebra. -/
theorem torTwoTerm1Coprod_map_smul (P : Presentation A B ι σ) (r : B)
    (x : torTwoTerm1SourceModuleCat P) :
    torTwoTerm1Coprod P (r • x) = r • torTwoTerm1Coprod P x := sorry

/-- The linear sum of the exterior, mixed, and degeneracy tensor maps. -/
def torTwoTerm1CoprodLM (P : Presentation A B ι σ) :
    torTwoTerm1SourceModuleCat P →ₗ[B] term1MulKerModuleCat P where
  toFun := torTwoTerm1Coprod P
  map_add' := (torTwoTerm1Coprod P).map_add
  map_smul' := torTwoTerm1Coprod_map_smul P

/-- The specified three-summand linear tensor map is bijective. -/
theorem torTwoTerm1Coprod_bijective (P : Presentation A B ι σ) :
    Function.Bijective (torTwoTerm1CoprodLM P) := sorry

/-- The multiplication-kernel map induced by the zero face. -/
def faceZeroMulKer (P : Presentation A B ι σ) :
    term1MulKerModuleCat P →+ term0MulKerModuleCat P :=
  mulKerMap (faceZero P).toRingHom (fun _ hp => faceZero_mem_ker P hp)

/-- The multiplication-kernel map induced by the one face. -/
def faceOneMulKer (P : Presentation A B ι σ) :
    term1MulKerModuleCat P →+ term0MulKerModuleCat P :=
  mulKerMap (faceOne P).toRingHom (fun _ hp => faceOne_mem_ker P hp)

/-- The difference of the zero and one faces on multiplication kernels. -/
def faceSub (P : Presentation A B ι σ) :
    term1MulKerModuleCat P →+ term0MulKerModuleCat P :=
  faceZeroMulKer P - faceOneMulKer P

/-- The face difference vanishes on the degeneracy summand. -/
theorem faceSub_degeneracyIncl (P : Presentation A B ι σ) :
    (faceSub P).comp (degeneracyIncl P) = 0 := sorry

/-- The mixed face image is the alternating tensor of an ideal element and its chosen relation. -/
theorem faceSub_mixedIncl (P : Presentation A B ι σ) (t : σ) (f : P.ker) :
    faceSub P (mixedIncl P (Finsupp.single t (P.ker.toCotangent f))) =
      alternTmul f (relationKer P t) := sorry

/-- The exterior face image reverses the order of the two chosen relations. -/
theorem faceSub_wedgeIncl (P : Presentation A B ι σ) (t t' : σ) :
    faceSub P (wedgeIncl P (exteriorPower.ιMulti B 2 fun i =>
      Finsupp.single (if i = 0 then t else t') (1 : B))) =
      alternTmul (relationKer P t') (relationKer P t) := sorry

/-- The face difference is linear over the presented algebra. -/
theorem faceSub_map_smul (P : Presentation A B ι σ) (r : B) (x : term1MulKerModuleCat P) :
    faceSub P (r • x) = r • faceSub P x := sorry

/-- The linear face difference between the two multiplication-kernel modules. -/
def faceSubLM (P : Presentation A B ι σ) :
    term1MulKerModuleCat P →ₗ[B] term0MulKerModuleCat P where
  toFun := faceSub P
  map_add' := (faceSub P).map_add
  map_smul' := faceSub_map_smul P

/-- The module cokernel of the difference of the two faces. -/
def cokerFaceSub (P : Presentation A B ι σ) : ModuleCat.{u} B :=
  cokernel (ModuleCat.ofHom (faceSubLM P))

/-- The canonical linear projection to the face cokernel. -/
def cokerFaceSubMkQ (P : Presentation A B ι σ) :
    term0MulKerModuleCat P →ₗ[B] cokerFaceSub P :=
  (cokernel.π (ModuleCat.ofHom (faceSubLM P))).hom

/-- The conormal exterior comparison is exact at the multiplication kernel. -/
theorem exact_conormalExteriorSquare_cokerFaceSub (P : Presentation A B ι σ) :
    Function.Exact (conormalExteriorSquareToMulKer P.ker) (cokerFaceSubMkQ P) := sorry

/-- The canonical projection onto the face cokernel is surjective. -/
theorem cokerFaceSubMkQ_surjective (P : Presentation A B ι σ) :
    Function.Surjective (cokerFaceSubMkQ P) := sorry

end Algebra.Presentation.LengthTwo
