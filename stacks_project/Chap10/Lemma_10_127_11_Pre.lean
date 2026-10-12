/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import stacks_project.Chap10.Lemma_10_127_10
public import ReasLib.RingTheory.DirectLimit.Tail

/-!
# Support for prime-localization transitions in local approximations

@stack 00QV

This compatibility leaf retains only the data and statement interfaces used by
the source-facing approximation and tail constructions.
-/

@[expose] public section

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w uR uS

section

variable {R : Type uR} {S : Type uS} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]

/-
Domain sampling:
* Primary domain: directed approximation systems for local homomorphisms of local rings in
  commutative algebra.
* Owner declarations inspected in this domain:
  - `DirectedLocalHomApproximation`
  - `DirectedLocalHomApproximation.targetStageBaseChange`
  - `DirectedLocalHomApproximation.stageBaseChangeMap`
  - `RingHom.EssFinitePresentation`
* Best owner abstraction: `DirectedLocalHomApproximation f` is the source-facing approximation
  object; “the transition base-change maps are localizations at prime ideals” is derived
  transition behavior of that owner, not new primitive data from `Lemma_10_127_10`.
* Primitive vs. derived: the directed system, stage rings, local maps, and colimit identifications
  are primitive owner data from `Lemma_10_127_10`; prime-localization transition behavior is a
  property of those canonical base-change maps.
-/

namespace DirectedLocalHomApproximation

/-- A transition in a directed local approximation presents the later target stage as a
localization at a prime ideal of the corresponding base-change ring. -/
@[stacks 00QV "prime-localization transition property"]
def TransitionIsLocalizationAtPrime {f : R →+* S} (A : DirectedLocalHomApproximation f)
    {i j : A.Λ} (h : i ≤ j) : Prop :=
  ∃ q : Ideal (A.targetStageBaseChange h),
    ∃ _ : q.IsPrime, q.primeCompl.IsLocalizationMap (A.stageBaseChangeMap h)

/-- Every transition in a directed local approximation is a localization at a prime ideal. -/
@[stacks 00QV "prime-localization transition property"]
abbrev HasPrimeLocalizationTransitions {f : R →+* S} (A : DirectedLocalHomApproximation f) : Prop :=
  ∀ {i j : A.Λ} (h : i ≤ j), A.TransitionIsLocalizationAtPrime h

/-- A directed local approximation has a transition whose canonical base-change map is not a
localization at a prime ideal. -/
@[stacks 00QV "failure of prime-localization transition property"]
def HasFailingPrimeLocalizationTransition {f : R →+* S} (A : DirectedLocalHomApproximation f) :
    Prop :=
  ∃ (i j : A.Λ) (h : i ≤ j), ¬ A.TransitionIsLocalizationAtPrime h

end DirectedLocalHomApproximation

variable (f : R →+* S) [IsLocalHom f]

/-- Helper for Lemma 10.127.11: localizing a ring at a submonoid and then localizing the result at
the complement of its maximal ideal is the same as localizing the source at the pulled-back prime.
-/
theorem local_isLocalization_at_comap_maximalIdeal
    {P : Type v} {T : Type w} [CommRing P] [CommRing T] [Algebra P T]
    (M : Submonoid P) [IsLocalization M T] [IsLocalRing T] :
    let q : Ideal P := Ideal.comap (algebraMap P T) (IsLocalRing.maximalIdeal T)
    q.IsPrime ∧ q.primeCompl.IsLocalizationMap (algebraMap P T) := sorry


namespace DirectedLocalHomApproximation

omit [IsLocalRing R] [IsLocalRing S] in
/-- Helper for Lemma 10.127.11: the owner base-change map multiplies the target transition and
the later stage map on pure tensors, for any directed local approximation. -/
theorem stageBaseChangeMap_tmul' {f' : R →+* S} (A' : DirectedLocalHomApproximation f')
    {i j : A'.Λ} (h : i ≤ j) :
    let _ : Algebra (A'.toApproximation.source i) (A'.toApproximation.target i) :=
      (A'.stageMap i).toAlgebra
    let _ : Algebra (A'.toApproximation.source i) (A'.toApproximation.source j) :=
      (A'.map i j h).toAlgebra
    ∀ (s : A'.toApproximation.target i) (r : A'.toApproximation.source j),
      A'.toApproximation.baseChangeMap h (s ⊗ₜ[A'.toApproximation.source i] r) =
        A'.toApproximation.targetMap i j h s * A'.toApproximation.map j r := sorry

end DirectedLocalHomApproximation

/-- The elements outside the maximal ideal of a local ring are units. -/
theorem isUnit_of_mem_primeCompl_maximalIdeal
    (T : Type*) [CommRing T] [IsLocalRing T] (x : T)
    (hx : x ∈ (IsLocalRing.maximalIdeal T).primeCompl) : IsUnit x := sorry

/-- Helper for Lemma 10.127.11: the localization of a local ring at its maximal ideal collapses
back to the ring itself. -/
noncomputable def maxLocalizationCollapse (T : Type*) [CommRing T] [IsLocalRing T] :
    Localization.AtPrime (IsLocalRing.maximalIdeal T) ≃ₐ[T] T :=
  (IsLocalization.atUnits T (IsLocalRing.maximalIdeal T).primeCompl
    (isUnit_of_mem_primeCompl_maximalIdeal T)).symm

/-- Helper for Lemma 10.127.11: the collapse equivalence restricts to the identity on the original
local ring. -/
@[simp] theorem maxLocalizationCollapse_algebraMap (T : Type*) [CommRing T] [IsLocalRing T]
    (t : T) :
    maxLocalizationCollapse T
        (algebraMap T (Localization.AtPrime (IsLocalRing.maximalIdeal T)) t) = t := sorry
/-- Helper for Lemma 10.127.11: if two stage comparisons to the final local target differ only by
precomposition with a transition map, then the pulled-back maximal ideals differ by the same
comap. -/
theorem comap_contracted_maximalIdeal_eq_of_comp
    {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    (τ : A →+* B) (σA : A →+* S) (σB : B →+* S) (hcomp : σA = σB.comp τ) :
    Ideal.comap τ (Ideal.comap σB (IsLocalRing.maximalIdeal S)) =
      Ideal.comap σA (IsLocalRing.maximalIdeal S) := sorry
/-- Helper for Lemma 10.127.11: if a directed family of stage maps to a fixed local target is
compatible with the transition maps, then the induced prime localizations at the contracted
maximal ideals form a directed system. -/
theorem localized_contracted_maximalIdeal_directedSystem
    {Λ : Type v} [Preorder Λ] [Nonempty Λ]
    (G : Λ → Type w) [∀ i, CommRing (G i)]
    (map : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ map i j h)]
    (σ : (i : Λ) → G i →+* S)
    (hσ : ∀ i j (hij : i ≤ j), σ i = (σ j).comp (map i j hij)) :
    let q : (i : Λ) → Ideal (G i) := fun i ↦ Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)
    DirectedSystem (fun i ↦ Localization.AtPrime (q i))
      (fun i j hij ↦
        Localization.localRingHom (q i) (q j) (map i j hij)
          ((comap_contracted_maximalIdeal_eq_of_comp
            (S := S) (τ := map i j hij) (σA := σ i) (σB := σ j) (hσ i j hij)).symm)) := sorry
/-- Helper for Lemma 10.127.11: compatible stage maps to a fixed local target induce compatible
maps from the corresponding prime localizations cut out by the target maximal ideal. -/
theorem localized_stage_maps_to_ambient_compatible
    {Λ : Type v} [Preorder Λ]
    (G : Λ → Type w) [∀ i, CommRing (G i)]
    (map : ∀ i j, i ≤ j → G i →+* G j)
    (σ : (i : Λ) → G i →+* S)
    (hσ : ∀ i j (hij : i ≤ j), σ i = (σ j).comp (map i j hij)) :
    let q : (i : Λ) → Ideal (G i) := fun i ↦ Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)
    let ρ :
        ∀ i j, i ≤ j → Localization.AtPrime (q i) →+* Localization.AtPrime (q j) :=
      fun i j hij ↦
        Localization.localRingHom (q i) (q j) (map i j hij)
          ((comap_contracted_maximalIdeal_eq_of_comp
            (S := S) (τ := map i j hij) (σA := σ i) (σB := σ j) (hσ i j hij)).symm)
    let φ : (i : Λ) → Localization.AtPrime (q i) →+* S :=
      fun i ↦ (maxLocalizationCollapse S :
          Localization.AtPrime (IsLocalRing.maximalIdeal S) →+* S).comp
        (Localization.localRingHom (q i) (IsLocalRing.maximalIdeal S) (σ i) rfl)
    ∀ i j (hij : i ≤ j), φ i = (φ j).comp (ρ i j hij) := sorry

/-- Pointwise compatibility needed by the direct-limit lift of the localized stage maps. -/
theorem localized_stage_maps_to_ambient_compatible_apply
    {Λ : Type v} [Preorder Λ]
    (G : Λ → Type w) [∀ i, CommRing (G i)]
    (map : ∀ i j, i ≤ j → G i →+* G j)
    (σ : (i : Λ) → G i →+* S)
    (hσ : ∀ i j (hij : i ≤ j), σ i = (σ j).comp (map i j hij))
    (i j : Λ) (hij : i ≤ j)
    (x : Localization.AtPrime (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S))) :
    let q : (i : Λ) → Ideal (G i) :=
      fun i ↦ Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)
    let ρ : ∀ i j, i ≤ j → Localization.AtPrime (q i) →+* Localization.AtPrime (q j) :=
      fun i j hij ↦ Localization.localRingHom (q i) (q j) (map i j hij)
        ((comap_contracted_maximalIdeal_eq_of_comp
          (S := S) (τ := map i j hij) (σA := σ i) (σB := σ j) (hσ i j hij)).symm)
    let φ : (i : Λ) → Localization.AtPrime (q i) →+* S :=
      fun i ↦ (maxLocalizationCollapse S :
          Localization.AtPrime (IsLocalRing.maximalIdeal S) →+* S).comp
        (Localization.localRingHom (q i) (IsLocalRing.maximalIdeal S) (σ i) rfl)
    φ j (ρ i j hij x) = φ i x := sorry

/-- Helper for Lemma 10.127.11: the compatible localized stage maps to `S` lift to a map from the
direct limit of the localized system. -/
noncomputable def tail_target_colimit_to_ambient
    {Λ : Type v} [Preorder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    (G : Λ → Type w) [∀ i, CommRing (G i)]
    (map : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ map i j h)]
    (σ : (i : Λ) → G i →+* S)
    (hσ : ∀ i j (hij : i ≤ j), σ i = (σ j).comp (map i j hij)) :
    let q : (i : Λ) → Ideal (G i) := fun i ↦ Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)
    let ρ :
        ∀ i j, i ≤ j → Localization.AtPrime (q i) →+* Localization.AtPrime (q j) :=
      fun i j hij ↦
        Localization.localRingHom (q i) (q j) (map i j hij)
          ((comap_contracted_maximalIdeal_eq_of_comp
            (S := S) (τ := map i j hij) (σA := σ i) (σB := σ j) (hσ i j hij)).symm)
    Ring.DirectLimit (fun i ↦ Localization.AtPrime (q i)) (fun i j h ↦ ρ i j h) →+* S :=
  let q : (i : Λ) → Ideal (G i) := fun i ↦ Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)
  let ρ :
      ∀ i j, i ≤ j → Localization.AtPrime (q i) →+* Localization.AtPrime (q j) :=
    fun i j hij ↦
      Localization.localRingHom (q i) (q j) (map i j hij)
        ((comap_contracted_maximalIdeal_eq_of_comp
          (S := S) (τ := map i j hij) (σA := σ i) (σB := σ j) (hσ i j hij)).symm)
  let φ : (i : Λ) → Localization.AtPrime (q i) →+* S :=
    fun i ↦ (maxLocalizationCollapse S :
        Localization.AtPrime (IsLocalRing.maximalIdeal S) →+* S).comp
      (Localization.localRingHom (q i) (IsLocalRing.maximalIdeal S) (σ i) rfl)
  -- Proof comment: the stagewise localized comparison maps are compatible, so the universal
  -- property of the direct limit assembles them into a single ambient comparison.
  Ring.DirectLimit.lift
    (fun i ↦ Localization.AtPrime (q i))
    (fun i j h ↦ ρ i j h)
    S
    φ
    (localized_stage_maps_to_ambient_compatible_apply
      (S := S) G map σ hσ)

/-- Helper for Lemma 10.127.11: the lifted ambient comparison map agrees with the given localized
stage map on each direct-limit generator. -/
@[simp] theorem tail_target_colimit_to_ambient_of
    {Λ : Type v} [Preorder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    (G : Λ → Type w) [∀ i, CommRing (G i)]
    (map : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ map i j h)]
    (σ : (i : Λ) → G i →+* S)
    (hσ : ∀ i j (hij : i ≤ j), σ i = (σ j).comp (map i j hij))
    (i : Λ) (x : Localization.AtPrime (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S))) :
    tail_target_colimit_to_ambient (S := S) G map σ hσ
        (Ring.DirectLimit.of
          (fun i ↦ Localization.AtPrime (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)))
          (fun i j hij ↦
            Localization.localRingHom
              (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S))
              (Ideal.comap (σ j) (IsLocalRing.maximalIdeal S))
              (map i j hij)
              ((comap_contracted_maximalIdeal_eq_of_comp
                (S := S) (τ := map i j hij) (σA := σ i) (σB := σ j) (hσ i j hij)).symm))
          i x) =
      (maxLocalizationCollapse S :
          Localization.AtPrime (IsLocalRing.maximalIdeal S) →+* S)
        (Localization.localRingHom
          (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S))
          (IsLocalRing.maximalIdeal S)
          (σ i)
          rfl
          x) := sorry
end

section SameUniverse

variable {R S : Type u} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
variable (f : R →+* S) [IsLocalHom f]

omit [IsLocalRing R] in
/-- Helper for Lemma 10.127.11: a finitely presented algebra over the colimit ring descends to a
finitely presented algebra over some stage, up to base change. -/
theorem finitelyPresented_algebra_descends
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    (RStage : Λ → Type u) [∀ i, CommRing (RStage i)]
    (map : ∀ i j, i ≤ j → RStage i →+* RStage j)
    [DirectedSystem RStage (fun i j h ↦ map i j h)]
    (colimitIso : Ring.DirectLimit RStage (fun i j h ↦ map i j h) ≃+* R)
    (P : Type u) [CommRing P] [Algebra R P] [Algebra.FinitePresentation R P] :
    ∃ (i₀ : Λ) (P₀ : Type u) (_ : CommRing P₀) (_ : Algebra (RStage i₀) P₀)
      (_ : Algebra.FinitePresentation (RStage i₀) P₀),
      letI : Algebra (RStage i₀) R :=
        (Ring.DirectLimit.toLimitHom RStage (fun i j h ↦ map i j h) colimitIso i₀).toAlgebra
      letI : Algebra R (P₀ ⊗[RStage i₀] R) := Algebra.TensorProduct.rightAlgebra
      Nonempty (P₀ ⊗[RStage i₀] R ≃ₐ[R] P) := sorry
omit [IsLocalRing R] [IsLocalRing S] in
/-- Helper for Lemma 10.127.11: if the base-change domain of a transition is identified with a
prime localization and the transported owner map is the canonical localization map, then that
transition is a localization at a prime ideal. -/
theorem transitionIsLocalizationAtPrime_of_domain_equiv
    {f : R →+* S} (A : DirectedLocalHomApproximation f) {i j : A.Λ} (h : i ≤ j)
    {T : Type*} [CommRing T] (e : A.targetStageBaseChange h ≃+* T)
    (p : Ideal T) [p.IsPrime]
    (hmap :
      p.primeCompl.IsLocalizationMap ((A.stageBaseChangeMap h).comp e.symm.toRingHom)) :
    A.TransitionIsLocalizationAtPrime h := sorry
-- Proof sketch: choose an essentially finitely presented local presentation of `S` over `R`,
-- write `R` as a directed colimit of local rings essentially of finite type over `ℤ`, descend the
-- finitely many generators and relations of the presentation to a sufficiently large stage, and
-- localize at the inverse images of the chosen prime.
/-- If `T₁` is a localization of `T₀` at `M₀`, and the composite `g ∘ α` presents the local ring
`U` as the localization of `T₀` at a prime `qk'` containing no element of `M₀`, then `g` presents
`U` as a localization of `T₁` at a prime. -/
theorem isLocalizationMap_of_localization_tower
    {T₀ T₁ U : Type u} [CommRing T₀] [CommRing T₁] [CommRing U] [IsLocalRing U]
    (α : T₀ →+* T₁) (g : T₁ →+* U) (M₀ : Submonoid T₀)
    (qk' : Ideal T₀) (hqk'_prime : qk'.IsPrime)
    (hM₀ : M₀ ≤ qk'.primeCompl)
    (hT₁ : @IsLocalization T₀ _ M₀ T₁ _ α.toAlgebra)
    (hU : @IsLocalization.AtPrime T₀ _ U _ (g.comp α).toAlgebra qk' hqk'_prime) :
    ∃ q : Ideal T₁, ∃ _ : q.IsPrime, q.primeCompl.IsLocalizationMap g := sorry
/-- Helper for Lemma 10.127.11: the iterated base change of a descended algebra along the
directed system collapses to a single base change. -/
noncomputable def rawTensorCancel
    {Λ : Type u} [Preorder Λ]
    (RStage : Λ → Type u) [∀ i, CommRing (RStage i)]
    (map : ∀ i j, i ≤ j → RStage i →+* RStage j)
    (P₀ : Type u) [CommRing P₀] {i₀ j k : Λ} (hij : i₀ ≤ j) (hik : i₀ ≤ k) (hjk : j ≤ k)
    [Algebra (RStage i₀) P₀]
    (hcomp : (map j k hjk).comp (map i₀ j hij) = map i₀ k hik) :
    letI : Algebra (RStage i₀) (RStage j) := (map i₀ j hij).toAlgebra
    letI : Algebra (RStage i₀) (RStage k) := (map i₀ k hik).toAlgebra
    letI : Algebra (RStage j) (RStage k) := (map j k hjk).toAlgebra
    (P₀ ⊗[RStage i₀] RStage j) ⊗[RStage j] RStage k ≃+* P₀ ⊗[RStage i₀] RStage k :=
  letI : Algebra (RStage i₀) (RStage j) := (map i₀ j hij).toAlgebra
  letI : Algebra (RStage i₀) (RStage k) := (map i₀ k hik).toAlgebra
  letI : Algebra (RStage j) (RStage k) := (map j k hjk).toAlgebra
  letI : IsScalarTower (RStage i₀) (RStage j) (RStage k) :=
    IsScalarTower.of_algebraMap_eq' hcomp.symm
  -- Proof comment: commute the outer factors, commute the inner factors, cancel the middle base
  -- change, and commute back.
  ((Algebra.TensorProduct.comm (RStage j) (P₀ ⊗[RStage i₀] RStage j) (RStage k)).toRingEquiv).trans
    (((Algebra.TensorProduct.congr (AlgEquiv.refl (R := RStage j) (A₁ := RStage k))
      (AlgEquiv.ofRingEquiv
        (f := (Algebra.TensorProduct.comm (RStage i₀) P₀ (RStage j)).toRingEquiv)
        (fun x ↦ Algebra.TensorProduct.comm_tmul (RStage i₀) (1 : P₀) x))).toRingEquiv).trans
      (((Algebra.TensorProduct.cancelBaseChange (RStage i₀) (RStage j) (RStage j) (RStage k)
        P₀).toRingEquiv).trans
        ((Algebra.TensorProduct.comm (RStage i₀) (RStage k) P₀).toRingEquiv)))

/-- Helper for Lemma 10.127.11: a prime localization remains a prime localization after
precomposing the source ring with a ring equivalence and replacing the algebra map by an equal
ring homomorphism. -/
theorem isLocalization_atPrime_of_ringEquiv_source_map
    {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
    (e : A ≃+* B) (q : Ideal B) [q.IsPrime]
    [Algebra B T] [IsLocalization.AtPrime T q]
    (φ : A →+* T) (hφ : φ = (algebraMap B T).comp e.toRingHom) :
    let qA : Ideal A := Ideal.comap e.toRingHom q
    letI : qA.IsPrime := Ideal.comap_isPrime e.toRingHom q
    letI : Algebra A T := φ.toAlgebra
    IsLocalization.AtPrime T qA := sorry
/-- L1: assemble a ring map out of a base-change algebra `P ≅ P₀ ⊗ R` from compatible factor maps. -/
noncomputable def descentPsi
    {R₀ P₀ R' P' C : Type u} [CommRing R₀] [CommRing P₀] [CommRing R'] [CommRing P'] [CommRing C]
    [Algebra R₀ P₀] [Algebra R₀ R'] [Algebra R₀ C] [Algebra R' P']
    (e : P₀ ⊗[R₀] R' ≃ₐ[R'] P') (fP₀ : P₀ →ₐ[R₀] C) (fR : R' →ₐ[R₀] C) : P' →+* C :=
  (Algebra.TensorProduct.productMap fP₀ fR).toRingHom.comp e.symm.toRingHom

theorem descentPsi_apply
    {R₀ P₀ R' P' C : Type u} [CommRing R₀] [CommRing P₀] [CommRing R'] [CommRing P'] [CommRing C]
    [Algebra R₀ P₀] [Algebra R₀ R'] [Algebra R₀ C] [Algebra R' P']
    (e : P₀ ⊗[R₀] R' ≃ₐ[R'] P') (fP₀ : P₀ →ₐ[R₀] C) (fR : R' →ₐ[R₀] C) (p : P₀) (r : R') :
    descentPsi e fP₀ fR (e (p ⊗ₜ[R₀] r)) = fP₀ p * fR r := sorry
/-- Helper for Lemma 10.127.11: two equal `R`-algebra structures on the left tensor factor give a
ring isomorphism of the resulting base-change rings. (Used to bridge the record's
`(stageMap).toAlgebra` view with the canonical localization algebra, which are equal as instances
but not definitionally so.) -/
def tensorRingEquivOfAlgEq {R Sj Rk : Type u}
    [CommRing R] [CommRing Sj] [CommRing Rk] [Algebra R Rk]
    (alg1 alg2 : Algebra R Sj) (halg : alg1 = alg2) :
    (letI := alg1; (Sj ⊗[R] Rk)) ≃+* (letI := alg2; (Sj ⊗[R] Rk)) :=
  match halg with
  | rfl => RingEquiv.refl _

/-- The reverse bridge of `tensorRingEquivOfAlgEq` as a named ring hom. Keeping this bridge
outside the large transition proof avoids re-synthesizing the tensor-product semiring instances
from the expanded owner record. -/
noncomputable def tensorRingHomOfAlgEqSymm {R Sj Rk : Type u}
    [CommRing R] [CommRing Sj] [CommRing Rk] [Algebra R Rk]
    (alg1 alg2 : Algebra R Sj) (halg : alg1 = alg2) :
    (letI := alg2; Sj ⊗[R] Rk) →+* (letI := alg1; Sj ⊗[R] Rk) :=
  (tensorRingEquivOfAlgEq alg1 alg2 halg).symm.toRingHom

/-- Tensor on the left by an explicit algebra hom and on the right by the identity, named so
transition proofs do not repeatedly synthesize the same map. -/
noncomputable def tensorMapLeft {R A B C : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] (φ : A →ₐ[R] C) :
    A ⊗[R] B →+* C ⊗[R] B :=
  (Algebra.TensorProduct.map φ (AlgHom.id R B)).toRingHom

/-- The owner base-change map after both explicit tensor normalizations has the expected
pure-tensor formula. -/
theorem stageBaseChangeMap_tensorBridge_tensorMapLeft_tmul
    {R' S' T : Type u} [CommRing R'] [CommRing S'] [CommRing T] {f' : R' →+* S'}
    (A' : DirectedLocalHomApproximation.{u, u, u} f') {i j : A'.Λ} (h : i ≤ j)
    [Algebra (A'.RStage i) T]
    (algStage : Algebra (A'.RStage i) (A'.SStage i))
    (hinst : (A'.stageMap i).toAlgebra = algStage)
    (φ : T →ₐ[A'.RStage i] A'.SStage i) (x : T) (y : A'.RStage j) :
    letI : Algebra (A'.RStage i) (A'.RStage j) := (A'.map i j h).toAlgebra
    letI : Algebra (A'.RStage i) (A'.SStage i) := algStage
    ((A'.stageBaseChangeMap h).comp
        (tensorRingHomOfAlgEqSymm (R := A'.RStage i) (Sj := A'.SStage i)
          (Rk := A'.RStage j) ((A'.stageMap i).toAlgebra) algStage hinst))
      (tensorMapLeft (R := A'.RStage i) (A := T) (B := A'.RStage j)
        (C := A'.SStage i) φ (x ⊗ₜ[A'.RStage i] y)) =
    A'.targetMap i j h (φ x) * A'.stageMap j y := sorry

/-- Helper for Lemma 10.127.11: the canonical localized target stage attached to a raw
tail stage and its comparison map to `S`. -/
abbrev localizedTailStage
    {Λ : Type u}
    (G : Λ → Type u) [∀ i, CommRing (G i)]
    (σ : (i : Λ) → G i →+* S) (i : Λ) : Type u :=
  Localization.AtPrime (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S))

/-- Helper for Lemma 10.127.11: the canonical transition map between localized target tail
stages. -/
noncomputable abbrev localizedTailMap
    {Λ : Type u} [Preorder Λ]
    (G : Λ → Type u) [∀ i, CommRing (G i)]
    (map : ∀ i j, i ≤ j → G i →+* G j)
    (σ : (i : Λ) → G i →+* S)
    (hσ : ∀ i j (hij : i ≤ j), σ i = (σ j).comp (map i j hij))
    (i j : Λ) (hij : i ≤ j) : localizedTailStage (S := S) G σ i →+*
      localizedTailStage (S := S) G σ j :=
  Localization.localRingHom
    (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S))
    (Ideal.comap (σ j) (IsLocalRing.maximalIdeal S))
    (map i j hij)
    ((comap_contracted_maximalIdeal_eq_of_comp
      (S := S) (τ := map i j hij) (σA := σ i) (σB := σ j) (hσ i j hij)).symm)

/-- Helper for Lemma 10.127.11: the raw descended tensor stage over a tail index. -/
abbrev descendedTailRawStage
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    (i₀ : A₀.Λ) (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    (j : Set.Ici i₀) : Type u :=
  letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
  P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1

/-- Helper for Lemma 10.127.11: the raw tensor transition map on descended tail stages. -/
noncomputable abbrev descendedTailRawMap
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    (i₀ : A₀.Λ) (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    (j k : Set.Ici i₀) (hjk : j ≤ k) :
    descendedTailRawStage A₀ i₀ P₀ j →+* descendedTailRawStage A₀ i₀ P₀ k :=
  letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
  letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.map i₀ k.1 k.2).toAlgebra
  (Algebra.TensorProduct.map (AlgHom.id P₀ P₀)
    { toRingHom := A₀.map j.1 k.1 hjk
      commutes' := fun x ↦
        DirectedSystem.map_map (f := fun i j h ↦ A₀.map i j h) j.2 hjk x } :
    _ →+* _)

/-- Helper for Lemma 10.127.11: the raw tensor cancellation formula specialized to the
canonical descended tail stages. Naming this specialization keeps later transition proofs from
expanding the iterated tensor-cancellation equivalence in a large owner-record context. -/
theorem descendedTailRawTensorCancel_tmul_right
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    (i₀ : A₀.Λ) (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    (j k : Set.Ici i₀) (hjk : j ≤ k)
    (hcomp : (A₀.map j.1 k.1 hjk).comp (A₀.map i₀ j.1 j.2) = A₀.map i₀ k.1 k.2)
    (x : descendedTailRawStage A₀ i₀ P₀ j) (r' : A₀.RStage k.1) :
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
    letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.map i₀ k.1 k.2).toAlgebra
    letI : Algebra (A₀.RStage j.1) (A₀.RStage k.1) := (A₀.map j.1 k.1 hjk).toAlgebra
    rawTensorCancel A₀.RStage (fun a b h ↦ A₀.map a b h) P₀
        j.2 k.2 hjk hcomp (x ⊗ₜ[A₀.RStage j.1] r') =
      descendedTailRawMap A₀ i₀ P₀ j k hjk x *
        ((1 : P₀) ⊗ₜ[A₀.RStage i₀] r') := sorry
/-- Helper for Lemma 10.127.11: the comparison from a raw tail stage to the descended
presentation over the colimit source. -/
noncomputable abbrev descendedTailPComp
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    {P : Type u} [CommRing P] [Algebra R P]
    (i₀ : A₀.Λ) (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (j : Set.Ici i₀) : descendedTailRawStage A₀ i₀ P₀ j →+* P :=
  letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
  letI : Algebra (A₀.RStage j.1) R :=
    (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h)
      A₀.colimitIso j.1).toAlgebra
  letI : IsScalarTower (A₀.RStage i₀) (A₀.RStage j.1) R :=
    Ring.DirectLimit.toLimit_isScalarTower_of_algebraMap_eq
      A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso j.2 hRalg
  e.toRingHom.comp
    (Algebra.TensorProduct.map (AlgHom.id P₀ P₀)
      (IsScalarTower.toAlgHom (A₀.RStage i₀) (A₀.RStage j.1) R) :
      _ →+* _)

/-- Helper for Lemma 10.127.11: the comparison from a raw tail stage to the final local target. -/
noncomputable abbrev descendedTailSigma
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    {P : Type u} [CommRing P] [Algebra R P] [Algebra P S]
    (i₀ : A₀.Λ) (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (j : Set.Ici i₀) : descendedTailRawStage A₀ i₀ P₀ j →+* S :=
  (algebraMap P S).comp (descendedTailPComp A₀ i₀ P₀ hRalg e j)

/-- Helper for Lemma 10.127.11: the canonical localized target stage of the descended tail
system. -/
abbrev descendedTailSStage
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    {P : Type u} [CommRing P] [Algebra R P] [Algebra P S]
    (i₀ : A₀.Λ) (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P) (j : Set.Ici i₀) : Type u :=
  localizedTailStage (S := S) (descendedTailRawStage A₀ i₀ P₀)
    (descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e) j

/-- Helper for Lemma 10.127.11: the canonical localized target transition of the descended tail
system. -/
noncomputable abbrev descendedTailTargetMap
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    {P : Type u} [CommRing P] [Algebra R P] [Algebra P S]
    (i₀ : A₀.Λ) (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (hσ_raw_comp : ∀ (j k : Set.Ici i₀) (hjk : j ≤ k),
      descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e j =
        (descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e k).comp
          (descendedTailRawMap A₀ i₀ P₀ j k hjk))
    (j k : Set.Ici i₀) (hjk : j ≤ k) :
    descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j →+*
      descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e k :=
  localizedTailMap (S := S) (descendedTailRawStage A₀ i₀ P₀)
    (descendedTailRawMap A₀ i₀ P₀)
    (descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e) hσ_raw_comp j k hjk

/-- Helper for Lemma 10.127.11: after passing to localized tail target stages, the
localized transition on a raw generator multiplied by a source-stage generator agrees with the
raw tensor cancellation map followed by the later localization. This packages the generator
calculation used to compare the owner base-change map with the explicit localization tower. -/
theorem descendedTailTargetMap_stageMap_mul_eq_cancel
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    {P : Type u} [CommRing P] [Algebra R P] [Algebra P S]
    (i₀ : A₀.Λ) (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (hσ_raw_comp : ∀ (j k : Set.Ici i₀) (hjk : j ≤ k),
      descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e j =
        (descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e k).comp
          (descendedTailRawMap A₀ i₀ P₀ j k hjk))
    (stageMapTail : (j : Set.Ici i₀) → A₀.RStage j.1 →+*
      descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j)
    (hstageMapTail_apply : ∀ (j : Set.Ici i₀) (x : A₀.RStage j.1),
      stageMapTail j x =
        algebraMap (descendedTailRawStage A₀ i₀ P₀ j)
          (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j)
          ((algebraMap (A₀.RStage j.1) (descendedTailRawStage A₀ i₀ P₀ j)) x))
    (j k : Set.Ici i₀) (hjk : j ≤ k)
    (hcomp : (A₀.map j.1 k.1 hjk).comp (A₀.map i₀ j.1 j.2) = A₀.map i₀ k.1 k.2)
    (x : descendedTailRawStage A₀ i₀ P₀ j) (r' : A₀.RStage k.1) :
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
    letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.map i₀ k.1 k.2).toAlgebra
    letI : Algebra (A₀.RStage j.1) (A₀.RStage k.1) := (A₀.map j.1 k.1 hjk).toAlgebra
    descendedTailTargetMap (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k hjk
        (algebraMap (descendedTailRawStage A₀ i₀ P₀ j)
          (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j) x) *
      stageMapTail k r' =
    algebraMap (descendedTailRawStage A₀ i₀ P₀ k)
      (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e k)
      (rawTensorCancel A₀.RStage (fun a b h ↦ A₀.map a b h) P₀
        j.2 k.2 hjk hcomp (x ⊗ₜ[A₀.RStage j.1] r')) := sorry
/-- Helper for Lemma 10.127.11: the canonical source-to-target direct-limit map induced by
stage maps on a tail. -/
noncomputable abbrev sourceToTargetDirectLimitOf
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (SStage : Set.Ici i₀ → Type u) [∀ j, CommRing (SStage j)]
    (targetMap : ∀ j k : Set.Ici i₀, j ≤ k → SStage j →+* SStage k)
    [DirectedSystem SStage (fun j k h ↦ targetMap j k h)]
    (stageMapTail : (j : Set.Ici i₀) → A₀.RStage j.1 →+* SStage j)
    (hcommTail : ∀ {j k : Set.Ici i₀} (hjk : j ≤ k),
      (stageMapTail k).comp (A₀.map j.1 k.1 hjk) =
        (targetMap j k hjk).comp (stageMapTail j)) :
    R →+* Ring.DirectLimit SStage (fun j k h ↦ targetMap j k h) :=
  (Ring.DirectLimit.map stageMapTail (fun _ _ h ↦ hcommTail h)).comp
    (Ring.DirectLimit.Tail.equivTo (fun i j h ↦ A₀.map i j h)
      i₀ A₀.colimitIso).symm.toRingHom

/-- Helper for Lemma 10.127.11: the source-to-target direct-limit map sends a source stage
generator to the corresponding target stage generator. -/
theorem sourceToTargetDirectLimit_stage_of
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (SStage : Set.Ici i₀ → Type u) [∀ j, CommRing (SStage j)]
    (targetMap : ∀ j k : Set.Ici i₀, j ≤ k → SStage j →+* SStage k)
    [DirectedSystem SStage (fun j k h ↦ targetMap j k h)]
    (stageMapTail : (j : Set.Ici i₀) → A₀.RStage j.1 →+* SStage j)
    (hcommTail : ∀ {j k : Set.Ici i₀} (hjk : j ≤ k),
      (stageMapTail k).comp (A₀.map j.1 k.1 hjk) =
        (targetMap j k hjk).comp (stageMapTail j))
    (i : Set.Ici i₀) (x : A₀.RStage i.1) :
    sourceToTargetDirectLimitOf A₀ i₀ SStage targetMap stageMapTail
      (fun {j} {k} hjk ↦ hcommTail hjk)
      (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h)
        A₀.colimitIso i.1 x) =
    Ring.DirectLimit.of SStage (fun j k h ↦ targetMap j k h) i (stageMapTail i x) := sorry
end SameUniverse
