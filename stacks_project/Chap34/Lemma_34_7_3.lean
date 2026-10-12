/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf.Stability
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 34.7.3

This chapter entry records the neutral fppf covering-stability API directly.
The reusable owners live in
`ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf.Stability`.
-/

open CategoryTheory CategoryTheory.Limits

universe u v w

/- Lemma 34.7.3 (1): an isomorphism gives a singleton fppf covering. -/
@[stacks 021O] #check
  (CategoryTheory.Precoverage.mem_coverings_of_isIso :
    ∀ {T T' : AlgebraicGeometry.Scheme.{u}} (f : T' ⟶ T) [IsIso f],
      Presieve.singleton f ∈ AlgebraicGeometry.Scheme.fppfPrecoverage.coverings T)

/- Lemma 34.7.3 (2): indexed composition preserves fppf coverings. -/
@[stacks 021O] #check
  (CategoryTheory.Precoverage.comp_mem_coverings.{v, w, u, u + 1}
      (J := AlgebraicGeometry.Scheme.fppfPrecoverage) :
    ∀ {ι : Type v} {T : AlgebraicGeometry.Scheme.{u}}
      {Tᵢ : ι → AlgebraicGeometry.Scheme.{u}} (f : (i : ι) → Tᵢ i ⟶ T)
      (hf : Presieve.ofArrows Tᵢ f ∈ AlgebraicGeometry.Scheme.fppfPrecoverage.coverings T)
      {J : ι → Type w}
      {Tᵢⱼ : (i : ι) → J i → AlgebraicGeometry.Scheme.{u}}
      (g : (i : ι) → (j : J i) → Tᵢⱼ i j ⟶ Tᵢ i)
      (hg : ∀ i, Presieve.ofArrows (Tᵢⱼ i) (g i) ∈
        AlgebraicGeometry.Scheme.fppfPrecoverage.coverings (Tᵢ i)),
      Presieve.ofArrows (fun ij : Sigma J ↦ Tᵢⱼ ij.1 ij.2)
        (fun ij : Sigma J ↦ g ij.1 ij.2 ≫ f ij.1) ∈
          AlgebraicGeometry.Scheme.fppfPrecoverage.coverings T)

/- Lemma 34.7.3 (3): pullback preserves fppf coverings. -/
@[stacks 021O] #check
  (AlgebraicGeometry.Scheme.fppfCovering_pullback :
    ∀ {T T' : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
      {Tᵢ : ι → AlgebraicGeometry.Scheme.{u}} (f : (i : ι) → Tᵢ i ⟶ T)
      (hf : Presieve.ofArrows Tᵢ f ∈ AlgebraicGeometry.Scheme.fppfPrecoverage.coverings T)
      (g : T' ⟶ T),
      Presieve.ofArrows (fun i ↦ pullback g (f i))
        (fun i ↦ pullback.fst g (f i)) ∈
          AlgebraicGeometry.Scheme.fppfPrecoverage.coverings T')
