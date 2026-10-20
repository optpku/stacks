module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import stacks_project.Chap92.Example_92_5_9_Terms
public import stacks_project.Chap92.Remark_92_12_6_MulKer

/-!
# Length-two tensors for Tor_2^{P_1}(B, B)

This leaf owns the augmentation `P1 → B`, the three summand inclusions of
`Tor_2^{P_1}(B, B)` in the length-two presentation, and the face operator `d0 - d1`.
-/

@[expose] public section

open Algebra
open Algebra.CotangentComplex
open MvPolynomial
open scoped TensorProduct

noncomputable section

universe u

namespace Algebra.Presentation.LengthTwo

variable {A B ι σ : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The augmentation `P1 → B` given by `aeval P.val ∘ d0`. -/
noncomputable def term1AlgHom (P : Presentation A B ι σ) : term1 P →ₐ[A] B :=
  (aeval P.val).comp (faceZero P)

/-- Unfolding `term1AlgHom` recovers composition of `d0` with the presentation map. -/
theorem term1AlgHom_eq (P : Presentation A B ι σ) :
    term1AlgHom P = (aeval P.val).comp (faceZero P) :=
  sorry

/-- The augmentation `term1AlgHom` is surjective. -/
theorem term1AlgHom_surjective (P : Presentation A B ι σ) :
    Function.Surjective (term1AlgHom P) :=
  sorry

/-- The `P1`-algebra structure on `B` induced by the unique augmentation `P1 → B`. -/
noncomputable instance instAlgebraTerm1 (P : Presentation A B ι σ) : Algebra (term1 P) B :=
  (term1AlgHom P).toAlgebra

/-- The kernel `J1 = Ker(P1 → B)`. -/
noncomputable def term1Ker (P : Presentation A B ι σ) : Ideal (term1 P) :=
  RingHom.ker (term1AlgHom P).toRingHom

/-- The `B`-module structure on `mulKer J1` transported along `term1AlgHom`. -/
noncomputable instance instModuleMulKerTerm1 (P : Presentation A B ι σ) :
    Module B (mulKer (term1Ker P)) :=
  moduleAlgebra (term1AlgHom P).toRingHom (term1AlgHom_surjective P)

/-- Unfolding `term1Ker` recovers the ring-hom kernel of `term1AlgHom`. -/
theorem term1Ker_eq (P : Presentation A B ι σ) :
    term1Ker P = RingHom.ker (term1AlgHom P).toRingHom :=
  sorry

/-- The generator `x_t` lies in `J1`. -/
theorem x_mem_term1Ker (P : Presentation A B ι σ) (t : σ) :
    x P t ∈ term1Ker P :=
  sorry

/-- The generator `x_t` as an element of `J1`. -/
noncomputable def xKer (P : Presentation A B ι σ) (t : σ) : term1Ker P :=
  ⟨x P t, x_mem_term1Ker P t⟩

/-- Unfolding `xKer` recovers `x_t`. -/
theorem xKer_coe (P : Presentation A B ι σ) (t : σ) :
    (xKer P t : term1 P) = x P t :=
  sorry

/-- The degeneracy `s0` sends `J0` into `J1`. -/
theorem degeneracyZero_mem_term1Ker (P : Presentation A B ι σ) {f : P.Ring}
    (hf : f ∈ P.ker) : degeneracyZero P f ∈ term1Ker P :=
  sorry

/-- The restriction of `s0` to kernels `J0 → J1`. -/
noncomputable def degeneracyZero_mapKer (P : Presentation A B ι σ) :
    P.ker →+ term1Ker P :=
  AddMonoidHom.codRestrict
    ((degeneracyZero P).toRingHom.toAddMonoidHom.comp
      (Submodule.subtype P.ker).toAddMonoidHom)
    (term1Ker P)
    (fun f => degeneracyZero_mem_term1Ker P f.2)

/-- The face `d0` sends `J1` into `J0`. -/
theorem faceZero_mem_ker (P : Presentation A B ι σ) {p : term1 P}
    (hp : p ∈ term1Ker P) : faceZero P p ∈ P.ker :=
  sorry

/-- The restriction of `d0` to kernels `J1 → J0`. -/
noncomputable def faceZero_mapKer (P : Presentation A B ι σ) :
    term1Ker P →+ P.ker :=
  AddMonoidHom.codRestrict
    ((faceZero P).toRingHom.toAddMonoidHom.comp
      (Submodule.subtype (term1Ker P)).toAddMonoidHom)
    P.ker
    (fun p => faceZero_mem_ker P p.2)

/-- The face `d1` sends `J1` into `J0`. -/
theorem faceOne_mem_ker (P : Presentation A B ι σ) {p : term1 P}
    (hp : p ∈ term1Ker P) : faceOne P p ∈ P.ker :=
  sorry

/-- The restriction of `d1` to kernels `J1 → J0`. -/
noncomputable def faceOne_mapKer (P : Presentation A B ι σ) :
    term1Ker P →+ P.ker :=
  AddMonoidHom.codRestrict
    ((faceOne P).toRingHom.toAddMonoidHom.comp
      (Submodule.subtype (term1Ker P)).toAddMonoidHom)
    P.ker
    (fun p => faceOne_mem_ker P p.2)

/-- The relation `f_t` as an element of `J0`. -/
theorem relation_mem_ker (P : Presentation A B ι σ) (t : σ) :
    P.relation t ∈ P.ker :=
  sorry

/-- The relation `f_t` packaged in `J0`. -/
noncomputable def relationKer (P : Presentation A B ι σ) (t : σ) : P.ker :=
  ⟨P.relation t, relation_mem_ker P t⟩

/-- An additive map of kernels induces a map of `mulKer` objects. -/
noncomputable def mapMulKer {R S : Type u} [CommRing R] [CommRing S]
    {I : Ideal R} {J : Ideal S} (φ : I →+ J) : mulKer I →+ mulKer J :=
  AddMonoidHom.codRestrict
    ((TensorProduct.liftAddHom
        { toFun := fun a =>
            { toFun := fun b => φ a ⊗ₜ φ b
              map_zero' := sorry
              map_add' := sorry }
          map_zero' := sorry
          map_add' := sorry }
        sorry).comp
      (Submodule.subtype (mulKer I)).toAddMonoidHom)
    (mulKer J)
    (fun _ => sorry)

/-- The alternating map sending a pair of finitely supported families to the corresponding
weighted sum of `x_t ⊗ x_{t'} - x_{t'} ⊗ x_t`. -/
noncomputable def wedgeInclAlternating (P : Presentation A B ι σ) :
    (σ →₀ B) [⋀^Fin 2]→ₗ[B] mulKer (term1Ker P) where
  toFun v :=
    (v 0).sum fun t a =>
      (v 1).sum fun t' b =>
        (a * b) • alternTmul (xKer P t) (xKer P t')
  map_update_add' := sorry
  map_update_smul' := sorry
  map_eq_zero_of_eq' := sorry

/-- The first summand inclusion, sending `e_t ∧ e_{t'}` to `x_t ⊗ x_{t'} - x_{t'} ⊗ x_t`. -/
noncomputable def wedgeIncl (P : Presentation A B ι σ) :
    ⋀[B]^2 (σ →₀ B) →+ mulKer (term1Ker P) :=
  (exteriorPower.alternatingMapLinearEquiv (wedgeInclAlternating P)).toAddMonoidHom

/-- On basis wedges, `wedgeIncl` recovers the alternating tensor of `x_t` and `x_{t'}`. -/
theorem wedgeIncl_apply (P : Presentation A B ι σ) (t t' : σ) :
    wedgeIncl P
        (exteriorPower.ιMulti B 2 fun i =>
          Finsupp.single (if i = 0 then t else t') (1 : B)) =
      alternTmul (xKer P t) (xKer P t') :=
  sorry

/-- The mixed inclusion on a single generator `t` and a kernel element `f`. -/
noncomputable def mixedInclSingle (P : Presentation A B ι σ) (t : σ) :
    P.ker →+ mulKer (term1Ker P) where
  toFun f := alternTmul (xKer P t) (degeneracyZero_mapKer P f)
  map_zero' := sorry
  map_add' := sorry

/-- The mixed inclusion on the conormal class of `f`. -/
noncomputable def mixedInclSingleCotangent (P : Presentation A B ι σ) (t : σ) :
    P.ker.Cotangent →+ mulKer (term1Ker P) where
  toFun x := Quotient.liftOn x (fun f => mixedInclSingle P t f) sorry
  map_zero' := sorry
  map_add' := sorry

/-- The second summand inclusion, sending the class of `x_t ⊗ f` to
`x_t ⊗ s0(f) - s0(f) ⊗ x_t`. -/
noncomputable def mixedIncl (P : Presentation A B ι σ) :
    (σ →₀ P.ker.Cotangent) →+ mulKer (term1Ker P) :=
  Finsupp.liftAddHom (mixedInclSingleCotangent P)

/-- On a representative `f ∈ J0`, `mixedIncl` recovers the mixed alternating tensor. -/
theorem mixedIncl_apply (P : Presentation A B ι σ) (t : σ) (f : P.ker) :
    mixedIncl P (Finsupp.single t (P.ker.toCotangent f)) =
      alternTmul (xKer P t) (degeneracyZero_mapKer P f) :=
  sorry

/-- The mixed inclusion vanishes on classes coming from `J0²`. -/
theorem mixedIncl_apply_eq_zero_of_mem_sq (P : Presentation A B ι σ) (t : σ) (f : P.ker)
    (hf : (f : P.Ring) ∈ P.ker ^ 2) :
    mixedIncl P (Finsupp.single t (P.ker.toCotangent f)) = 0 :=
  sorry

/-- The degeneracy `s0` on `Tor_2^{P_0}(B, B) → Tor_2^{P_1}(B, B)`. -/
noncomputable def degeneracyIncl (P : Presentation A B ι σ) :
    mulKer P.ker →+ mulKer (term1Ker P) :=
  mapMulKer (degeneracyZero_mapKer P)

/-- The coproduct of the three summand inclusions. -/
noncomputable def torTwoTerm1Coprod (P : Presentation A B ι σ) :
    (⋀[B]^2 (σ →₀ B)) × (σ →₀ P.ker.Cotangent) × mulKer P.ker →+ mulKer (term1Ker P) :=
  (wedgeIncl P).coprod ((mixedIncl P).coprod (degeneracyIncl P))


/-- The face operator `d0` on `mulKer`. -/
noncomputable def faceZeroMulKer (P : Presentation A B ι σ) :
    mulKer (term1Ker P) →+ mulKer P.ker :=
  mapMulKer (faceZero_mapKer P)

/-- The face operator `d1` on `mulKer`. -/
noncomputable def faceOneMulKer (P : Presentation A B ι σ) :
    mulKer (term1Ker P) →+ mulKer P.ker :=
  mapMulKer (faceOne_mapKer P)

/-- The operator `d0 - d1` on `Tor_2^{P_1}(B, B) → Tor_2^{P_0}(B, B)`. -/
noncomputable def faceSub (P : Presentation A B ι σ) :
    mulKer (term1Ker P) →+ mulKer P.ker :=
  faceZeroMulKer P - faceOneMulKer P

/-- The map `d0 - d1` vanishes on the image of `s0`. -/
theorem faceSub_degeneracyIncl (P : Presentation A B ι σ) :
    (faceSub P).comp (degeneracyIncl P) = 0 :=
  sorry

/-- On mixed tensors, `d0 - d1` sends `x_t ⊗ f` to `f ⊗ f_t - f_t ⊗ f`. -/
theorem faceSub_mixedIncl (P : Presentation A B ι σ) (t : σ) (f : P.ker) :
    faceSub P (mixedIncl P (Finsupp.single t (P.ker.toCotangent f))) =
      alternTmul f (relationKer P t) :=
  sorry

/-- On exterior generators, `d0 - d1` sends `x_t ∧ x_{t'}` to `f_{t'} ⊗ f_t - f_t ⊗ f_{t'}`. -/
theorem faceSub_wedgeIncl (P : Presentation A B ι σ) (t t' : σ) :
    faceSub P
        (wedgeIncl P
          (exteriorPower.ιMulti B 2 fun i =>
            Finsupp.single (if i = 0 then t else t') (1 : B))) =
      alternTmul (relationKer P t') (relationKer P t) :=
  sorry

/-- The subgroup generated by `(P0 / J0)`-multiples of the image of `d0 - d1`. -/
noncomputable def faceSubRange (P : Presentation A B ι σ) :
    AddSubgroup (mulKer P.ker) :=
  AddSubgroup.closure
    (Set.range fun p : (P.Ring ⧸ P.ker) × mulKer (term1Ker P) => p.1 • faceSub P p.2)

/-- The cokernel of `d0 - d1` on `Tor_2^{P_0}(B, B)`. -/
noncomputable abbrev cokerFaceSub (P : Presentation A B ι σ) :=
  mulKer P.ker ⧸ faceSubRange P

/-- The quotient map onto the cokernel of `d0 - d1`. -/
noncomputable def cokerFaceSubMkQ (P : Presentation A B ι σ) :
    mulKer P.ker →+ cokerFaceSub P :=
  QuotientAddGroup.mk' (faceSubRange P)

/-- The presentation kernel agrees with the kernel of `algebraMap P.Ring B`. -/
theorem presentation_ker_eq (P : Presentation A B ι σ) :
    P.ker = RingHom.ker (algebraMap P.Ring B) :=
  sorry

/-- The quotient map `P0 / J0 → B` induced by the presentation. -/
noncomputable def term0QuotToBase (P : Presentation A B ι σ) :
    P.Ring ⧸ P.ker →+* B :=
  Ideal.Quotient.lift P.ker (algebraMap P.Ring B) sorry

/-- The scalar identification `B ≃ P0 / J0`. -/
noncomputable def term0ScalarEquiv (P : Presentation A B ι σ) :
    B ≃+* (P.Ring ⧸ P.ker) :=
  (RingEquiv.ofBijective (term0QuotToBase P) sorry).symm

/-- The scalar identification `B ≃ P0 / J0` used to view the cokernel as a `B`-module. -/
noncomputable abbrev cokerFaceSubScalarEquiv (P : Presentation A B ι σ) :
    B ≃+* (P.Ring ⧸ P.ker) :=
  term0ScalarEquiv P

/-- The `(P0 / J0)`-module structure on the cokernel of `d0 - d1`. -/
public noncomputable instance instModuleCokerFaceSub (P : Presentation A B ι σ) :
    Module (P.Ring ⧸ P.ker) (cokerFaceSub P) where
  smul r x := Quotient.liftOn x (fun m => cokerFaceSubMkQ P (r • m)) sorry
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- The `B`-module structure on `J0 / J0²` transported along `term0ScalarEquiv`. -/
public noncomputable instance instModuleKerCotangent (P : Presentation A B ι σ) :
    Module B P.ker.Cotangent :=
  Module.compHom P.ker.Cotangent (term0ScalarEquiv P).toRingHom

/-- The cokernel of `d0 - d1` as an object of `ModuleCat B`. -/
noncomputable def cokerFaceSubModuleCat (P : Presentation A B ι σ) : ModuleCat.{u} B :=
  @ModuleCat.of B _ (cokerFaceSub P) _
    (Module.compHom (cokerFaceSub P) (cokerFaceSubScalarEquiv P).toRingHom)

/-- The `B`-module structure on `mulKer J0` transported along `term0ScalarEquiv`. -/
public noncomputable instance instModuleMulKerTerm0 (P : Presentation A B ι σ) :
    Module B (mulKer P.ker) :=
  Module.compHom (mulKer P.ker) (term0ScalarEquiv P).toRingHom

/-- The three-summand source of the length-two `Tor_2^{P_1}` splitting, as a `B`-module. -/
public noncomputable def torTwoTerm1SourceModuleCat (P : Presentation A B ι σ) : ModuleCat.{u} B :=
  ModuleCat.of B ((⋀[B]^2 (σ →₀ B)) × (σ →₀ P.ker.Cotangent) × mulKer P.ker)

/-- `mulKer J1` as a `B`-module. -/
public noncomputable def torTwoTerm1TargetModuleCat (P : Presentation A B ι σ) : ModuleCat.{u} B :=
  ModuleCat.of B (mulKer (term1Ker P))

/-- The `B`-linear coproduct of the three summand inclusions. -/
public noncomputable def torTwoTerm1CoprodLM (P : Presentation A B ι σ) :
    ((⋀[B]^2 (σ →₀ B)) × (σ →₀ P.ker.Cotangent) × mulKer P.ker) →ₗ[B]
      mulKer (term1Ker P) where
  toFun := torTwoTerm1Coprod P
  map_add' := sorry
  map_smul' := sorry

/-- The three-summand `B`-linear coproduct is bijective. -/
public theorem torTwoTerm1Coprod_bijective (P : Presentation A B ι σ) :
    Function.Bijective (torTwoTerm1CoprodLM P) :=
  sorry

/-- The `B`-linear splitting of `Tor_2^{P_1}(B, B)` on a length-two presentation. -/
public noncomputable def torTwoTerm1LinearEquiv (P : Presentation A B ι σ) :
    ((⋀[B]^2 (σ →₀ B)) × (σ →₀ P.ker.Cotangent) × mulKer P.ker) ≃ₗ[B]
      mulKer (term1Ker P) :=
  { torTwoTerm1CoprodLM P,
    Equiv.ofBijective (torTwoTerm1CoprodLM P) (torTwoTerm1Coprod_bijective P) with }

/-- The `B`-linear equivalence has forward map `torTwoTerm1CoprodLM`. -/
public theorem torTwoTerm1LinearEquiv_toLinearMap (P : Presentation A B ι σ) :
    (torTwoTerm1LinearEquiv P).toLinearMap = torTwoTerm1CoprodLM P :=
  sorry

end Algebra.Presentation.LengthTwo
