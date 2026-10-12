/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Etale.Stability
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u v w

/- Lemma 34.4.3 (1): an isomorphism gives a singleton étale covering. -/
@[stacks 0217] #check
  (AlgebraicGeometry.Scheme.etaleCovering_singleton_of_isIso :
    ∀ {T T' : AlgebraicGeometry.Scheme.{u}} (f : T' ⟶ T) [IsIso f],
      Presieve.ofArrows (fun _ : Unit ↦ T') (fun _ : Unit ↦ f) ∈
        AlgebraicGeometry.Scheme.etalePrecoverage.coverings T)

/- Lemma 34.4.3 (2): indexed composition preserves étale coverings. -/
@[stacks 0217] #check
  (AlgebraicGeometry.Scheme.etaleCovering_comp :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v} {κ : ι → Type w}
      {Tᵢ : ι → AlgebraicGeometry.Scheme.{u}} (f : (i : ι) → Tᵢ i ⟶ T)
      (hf : Presieve.ofArrows Tᵢ f ∈ AlgebraicGeometry.Scheme.etalePrecoverage.coverings T)
      {Tᵢⱼ : (i : ι) → κ i → AlgebraicGeometry.Scheme.{u}}
      (g : (i : ι) → (j : κ i) → Tᵢⱼ i j ⟶ Tᵢ i)
      (hg : ∀ i, Presieve.ofArrows (Tᵢⱼ i) (g i) ∈
        AlgebraicGeometry.Scheme.etalePrecoverage.coverings (Tᵢ i)),
      Presieve.ofArrows (fun ij : Sigma κ ↦ Tᵢⱼ ij.1 ij.2)
        (fun ij : Sigma κ ↦ g ij.1 ij.2 ≫ f ij.1) ∈
          AlgebraicGeometry.Scheme.etalePrecoverage.coverings T)

/- Lemma 34.4.3 (3): base change along any scheme morphism preserves étale coverings. -/
@[stacks 0217] #check
  (AlgebraicGeometry.Scheme.etaleCovering_pullback :
    ∀ {T T' : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
      {Tᵢ : ι → AlgebraicGeometry.Scheme.{u}} (f : (i : ι) → Tᵢ i ⟶ T)
      (hf : Presieve.ofArrows Tᵢ f ∈ AlgebraicGeometry.Scheme.etalePrecoverage.coverings T)
      (g : T' ⟶ T),
      Presieve.ofArrows (fun i ↦ pullback g (f i))
        (fun i ↦ pullback.fst g (f i)) ∈
          AlgebraicGeometry.Scheme.etalePrecoverage.coverings T')
