module

public import ReasLib.RingTheory.DirectLimit.Tail
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import stacks_project.Chap10.Lemma_10_127_11_Tower_Local

/-!
# Lemma 10.127.11 transition tower support

@stack 00QV

This leaf contains the statement-level tensor bridge and the final packaging interface used by
the source-facing approximation entry point.
-/

@[expose] public section

open scoped TensorProduct Algebra.TensorProduct.Right

universe u

section SameUniverse

variable {R S : Type u} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
variable (f : R →+* S) [IsLocalHom f]

/-- Helper for the transition tower: the pure-tensor formula for the owner base-change map,
with the owner fields rewritten by pointwise equalities rather than dependent function rewrites. -/
theorem stageBaseChangeMap_tensorBridge_tensorMapLeft_tmul_pointwise
    {R' S' T : Type u} [CommRing R'] [CommRing S'] [CommRing T] {f' : R' →+* S'}
    (A' : DirectedLocalHomApproximation.{u, u, u} f') {i j : A'.Λ} (h : i ≤ j)
    [Algebra (A'.RStage i) T]
    (algStage : Algebra (A'.RStage i) (A'.SStage i))
    (hinst : (A'.stageMap i).toAlgebra = algStage)
    (φ : T →ₐ[A'.RStage i] A'.SStage i)
    (targetMapIJ : A'.SStage i →+* A'.SStage j)
    (stageMapJ : A'.RStage j →+* A'.SStage j)
    (htarget : ∀ z : A'.SStage i, A'.targetMap i j h z = targetMapIJ z)
    (hstage : ∀ y : A'.RStage j, A'.stageMap j y = stageMapJ y)
    (x : T) (y : A'.RStage j) :
    letI : Algebra (A'.RStage i) (A'.RStage j) := (A'.map i j h).toAlgebra
    letI : Algebra (A'.RStage i) (A'.SStage i) := algStage
    ((A'.stageBaseChangeMap h).comp
        (tensorRingHomOfAlgEqSymm (R := A'.RStage i) (Sj := A'.SStage i)
          (Rk := A'.RStage j) ((A'.stageMap i).toAlgebra) algStage hinst))
      (tensorMapLeft (R := A'.RStage i) (A := T) (B := A'.RStage j)
        (C := A'.SStage i) φ (x ⊗ₜ[A'.RStage i] y)) =
    targetMapIJ (φ x) * stageMapJ y := sorry

/-- Helper for Lemma 10.127.11: once the raw localized tail system has been constructed, package
it as a directed local approximation and prove that its transition base changes are prime
localizations. -/
theorem finish_localEssFinitePresentationApproximation
    (A₀ : DirectedLocalHomApproximation.{u, u, u} (RingHom.id R))
    {P : Type u} [CommRing P] [Algebra R P] (g : R →+* P) [Algebra P S]
    (q : Ideal P) [q.IsPrime]
    (hlocq : q.primeCompl.IsLocalizationMap (algebraMap P S))
    (hfg : f = (algebraMap P S).comp g)
    (i₀ : A₀.Λ) {P₀ : Type u} [CommRing P₀]
    [Algebra (A₀.RStage i₀) P₀] [Algebra (A₀.RStage i₀) R]
    [Algebra.FinitePresentation (A₀.RStage i₀) P₀]
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (hPalg : algebraMap R P = g)
    (rawDirectedSystem :
      DirectedSystem (descendedTailRawStage A₀ i₀ P₀)
        (fun j k h ↦ descendedTailRawMap A₀ i₀ P₀ j k h))
    (hσ_comp : ∀ j : Set.Ici i₀,
      (descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e j).comp
          (algebraMap (A₀.RStage j.1) (descendedTailRawStage A₀ i₀ P₀ j)) =
        f.comp (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h)
          A₀.colimitIso j.1))
    (hσ_raw_comp : ∀ (j k : Set.Ici i₀) (hjk : j ≤ k),
      descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e j =
        (descendedTailSigma (S := S) A₀ i₀ P₀ hRalg e k).comp
          (descendedTailRawMap A₀ i₀ P₀ j k hjk))
    (targetDirectedSystem :
      DirectedSystem (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e)
        (fun j k h ↦ descendedTailTargetMap (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k h))
    (stageMapTail : (j : Set.Ici i₀) → A₀.RStage j.1 →+*
      descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j)
    (hstageMapTail_apply : ∀ (j : Set.Ici i₀) (x : A₀.RStage j.1),
      stageMapTail j x =
        algebraMap (descendedTailRawStage A₀ i₀ P₀ j)
          (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e j)
          ((algebraMap (A₀.RStage j.1) (descendedTailRawStage A₀ i₀ P₀ j)) x))
    (hstageMapTail_local : ∀ j : Set.Ici i₀, IsLocalHom (stageMapTail j))
    (hstageMapTail_essFiniteType : ∀ j : Set.Ici i₀, (stageMapTail j).EssFiniteType)
    (hcommTail : ∀ {j k : Set.Ici i₀} (hjk : j ≤ k),
      (stageMapTail k).comp (A₀.map j.1 k.1 hjk) =
        (descendedTailTargetMap (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k hjk).comp
          (stageMapTail j))
    (hSourceStage : ∀ (i : Set.Ici i₀) (x : A₀.RStage i.1),
      sourceToTargetDirectLimitOf A₀ i₀
        (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e)
        (descendedTailTargetMap (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp)
        stageMapTail (fun {_ _} hjk ↦ hcommTail hjk)
        (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h)
          A₀.colimitIso i.1 x) =
      Ring.DirectLimit.of (descendedTailSStage (S := S) A₀ i₀ P₀ hRalg e)
        (fun j k h ↦ descendedTailTargetMap (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k h)
        i (stageMapTail i x)) :
    ∃ A : DirectedLocalHomApproximation.{u, u, u} f,
      DirectedLocalHomApproximation.HasPrimeLocalizationTransitions A := sorry

end SameUniverse
