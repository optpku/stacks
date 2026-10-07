module

public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import stacks_project.Chap10.Lemma_10_127_11_Pre.ApproximationBridge
public import stacks_project.Chap10.Lemma_10_127_11
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct Algebra.TensorProduct.Right

universe uR uS uM uN

section

variable {R : Type uR} {S : Type uS} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]

/-
Domain sampling:
* Primary domain: directed approximation systems for essentially finitely presented local
  homomorphisms together with descended finite stage modules.
* Owner declarations inspected in this domain:
  - `DirectedLocalHomApproximation`
  - `DirectedLocalHomApproximation.HasPrimeLocalizationTransitions`
  - `exists_localEssFinitePresentationApproximation`
  - `Ring.DirectLimit.Algebra.Approximation.Module`
  - `DirectedFinitePresentationModuleColimitApproximation`
* Best owner abstraction: the public owner for this source-facing module approximation should be a
  structure extending `DirectedLocalHomApproximation f`, exactly as the finite-presentation and
  colimit variants elsewhere in the chapter extend their ring-approximation owners.
* Layer targeted here: `source-facing` owner built over the chapter's `core/canonical`
  approximation owner `DirectedLocalHomApproximation f`.
* Primitive vs. derived: the source-facing primitive data are the stage modules `M_λ`, their
  finite `S_λ`-module structures, and the canonical transition/final base-change linear
  equivalences. Prime-localization transitions and the induced `R_λ`-module structures are
  derived from the inherited ring-approximation owner.
-/

variable (f : R →+* S) [IsLocalHom f]
variable {M : Type uM} [AddCommGroup M] [_root_.Module S M]

/- A directed approximation of a finitely presented `S`-module along an essentially finitely
presented local homomorphism `f : R →+* S`, with finite stage modules and canonical base-change
identifications along transitions and at the limit. -/
@[stacks 00QX "local finite-presentation module approximation"]
structure DirectedLocalHomApproximation.Module
    (f : R →+* S) (M : Type uM) [AddCommGroup M] [_root_.Module S M]
    extends DirectedLocalHomApproximation f where
  hasPrimeLocalizationTransitions :
    DirectedLocalHomApproximation.HasPrimeLocalizationTransitions
      toDirectedLocalHomApproximation
  moduleStage : Λ → Type uN
  moduleStageAddCommGroup : ∀ i, AddCommGroup (moduleStage i)
  moduleStageModule : ∀ i, _root_.Module (SStage i) (moduleStage i)
  moduleStageFinite : ∀ i, _root_.Module.Finite (SStage i) (moduleStage i)
  transitionBaseChange :
    ∀ {i j : Λ} (h : i ≤ j),
      let _ : Algebra (SStage i) (SStage j) := (targetMap i j h).toAlgebra
      SStage j ⊗[SStage i] moduleStage i ≃ₗ[SStage j] moduleStage j
  finalBaseChange :
    ∀ i : Λ,
      let _ : Algebra (SStage i) S :=
        (DirectedLocalHomApproximation.targetStageToLimitHom
          toDirectedLocalHomApproximation i).toAlgebra
      S ⊗[SStage i] moduleStage i ≃ₗ[S] M

attribute [instance]
  DirectedLocalHomApproximation.Module.moduleStageAddCommGroup
attribute [instance]
  DirectedLocalHomApproximation.Module.moduleStageModule
attribute [instance]
  DirectedLocalHomApproximation.Module.moduleStageFinite

namespace DirectedLocalHomApproximation.Module

/-- The source-stage module action is obtained by restricting the target-stage
    action along the stage map. -/
@[stacks 00QX "source-stage module structure"]
instance stageModuleSource
    (A : DirectedLocalHomApproximation.Module f M) (i : A.Λ) :
    _root_.Module (A.RStage i) (A.moduleStage i) :=
  _root_.Module.compHom (A.moduleStage i) (A.stageMap i)

end DirectedLocalHomApproximation.Module

/-- Helper for Lemma 10.127.13: essential finite presentation for a mixed-universe local map
admits a descended finitely presented local model over a stage of an approximation of `id_R`. -/
@[stacks 00QX "mixed-universe local model descent"]
theorem exists_descended_local_finitePresentation_model_mixed_universe
    (hf : f.EssFinitePresentation) :
    ∃ (A₀ : DirectedLocalHomApproximation.{uR, uR, uR} (RingHom.id R))
      (_ : ∀ i j (h : i ≤ j), IsLocalHom (A₀.map i j h))
      (_ : ∀ i, IsLocalHom
        (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i))
      (P : Type uR) (_ : CommRing P) (_ : Algebra R P) (g : R →+* P) (_ : g.FinitePresentation)
      (_ : algebraMap R P = g)
      (q : Ideal P) (_ : q.IsPrime) (_ : Algebra P S),
      q.primeCompl.IsLocalizationMap (algebraMap P S) ∧
        f = (algebraMap P S).comp g ∧
        Ideal.comap g q = IsLocalRing.maximalIdeal R ∧
        ∃ (i₀ : A₀.Λ) (P₀ : Type uR) (_ : CommRing P₀)
          (_ : Algebra (A₀.RStage i₀) P₀) (_ : Algebra.FinitePresentation (A₀.RStage i₀) P₀),
          letI : Algebra (A₀.RStage i₀) R :=
            (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso
              i₀).toAlgebra
          Nonempty (P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P) := by
  letI : Algebra R S := f.toAlgebra
  have hfAlg : Algebra.EssFinitePresentation R S := hf
  rw [Algebra.essFinitePresentation_iff] at hfAlg
  rcases hfAlg with ⟨n, I, hI, _, _, M, hloc⟩
  let P : Type uR := MvPolynomial (Fin n) R ⧸ I
  let g : R →+* P := algebraMap R P
  have hg : g.FinitePresentation := by
    -- Proof comment: the quotient-model witness is finitely presented over `R`.
    rw [RingHom.finitePresentation_algebraMap]
    exact Algebra.FinitePresentation.quotient (R := R) (A := MvPolynomial (Fin n) R) hI
  let q : Ideal P := Ideal.comap (algebraMap P S) (IsLocalRing.maximalIdeal S)
  have hq :
      q.IsPrime ∧ q.primeCompl.IsLocalizationMap (algebraMap P S) := by
    -- Proof comment: replace the raw localization witness by the local prime localization cut out
    -- by the maximal ideal of `S`.
    simpa [q] using
      (local_isLocalization_at_comap_maximalIdeal (P := P) (T := S) (M := M))
  have hfg : f = (algebraMap P S).comp g := by
    -- Proof comment: the algebra tower from the quotient-model witness is exactly the original map
    -- `f`.
    simpa [g, RingHom.algebraMap_toAlgebra] using
      (IsScalarTower.algebraMap_eq R P S)
  have hPalg : algebraMap R P = g := by
    rfl
  have hqR : Ideal.comap g q = IsLocalRing.maximalIdeal R := by
    -- Proof comment: the factored local map pulls the contracted prime back to the maximal ideal
    -- of the local source.
    simpa [q, hfg, Ideal.comap_comap] using IsLocalRing.maximalIdeal_comap f
  have hid : (RingHom.id R).EssFiniteType := by
    -- Proof comment: the identity map is essentially finitely presented, hence essentially of
    -- finite type.
    rw [← Algebra.algebraMap_self (R := R), RingHom.essFiniteType_algebraMap]
    infer_instance
  obtain ⟨A₀, _, hA₀map, hA₀lim⟩ :=
    exists_directed_local_essFiniteType_approximation_isLocalHom (f := RingHom.id R) hid
  have hPfp : Algebra.FinitePresentation R P := by
    dsimp [P]
    exact Algebra.FinitePresentation.quotient (R := R) (A := MvPolynomial (Fin n) R) hI
  letI : Algebra.FinitePresentation R P := hPfp
  obtain ⟨i₀, P₀, _, _, _, e⟩ :=
    finitelyPresented_algebra_descends (R := R) A₀.RStage (fun i j h ↦ A₀.map i j h)
      A₀.colimitIso P
  exact ⟨A₀, hA₀map, hA₀lim, P, inferInstance, inferInstance, g, hg, hPalg, q, hq.1, inferInstance,
    hq.2, hfg, hqR,
    i₀, P₀, inferInstance, inferInstance, inferInstance, e⟩


end
