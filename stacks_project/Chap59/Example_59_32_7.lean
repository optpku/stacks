/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Henselian
public import ReasLib.RingTheory.PowerSeries.Etale
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

noncomputable section

/- Example 59.32.7 (1): every étale `PowerSeries ℂ`-algebra is a finite product
of trivial factors and factors `ℂ[[t]][T, T⁻¹] / (T ^ n - t)`, with the
displayed product decomposition preserving the base map. -/
@[stacks 03QI] #check (PowerSeries.etaleProductDecomposition :
    ∀ {S : Type u} [CommRing S] (f : PowerSeries ℂ →+* S), f.Etale →
      ∃ (I₀ I₁ : Type u) (_ : Fintype I₀) (_ : Fintype I₁)
        (n : I₁ → ℕ) (h_n : ∀ i, 0 < n i) (e : S ≃+*
          ((I₀ → PowerSeries ℂ) × (∀ i, PowerSeries.kummerFactor (n i)))),
        e.toRingHom.comp f = PowerSeries.productMap n)

/- Example 59.32.7 (2): each Laurent Kummer factor factors through the
localization at `t`, corresponding to the open `D(t) ⊂ Spec(ℂ[[t]])`. -/
@[stacks 03QI] #check (PowerSeries.kummerFactorsThroughDt :
    ∀ (n : ℕ), 0 < n →
      ∃ g : Localization.Away (PowerSeries.X : PowerSeries ℂ) →+*
        PowerSeries.kummerFactor n,
        g.comp (algebraMap (PowerSeries ℂ)
          (Localization.Away (PowerSeries.X : PowerSeries ℂ))) =
          PowerSeries.kummerMap n)

/- Example 59.32.7 (3): every étale covering of `Spec (PowerSeries ℂ)` is
refined by the identity covering. -/
@[stacks 03QI] #check (AlgebraicGeometry.Scheme.Etale.powerSeriesCoverRefinedByIdentity :
    ∀ (𝒰 : (Spec (.of (PowerSeries ℂ))).Cover Scheme.etalePrecoverage),
      ∃ i : 𝒰.I₀,
        ∃ s : Spec (.of (PowerSeries ℂ)) ⟶ 𝒰.X i,
          s ≫ 𝒰.f i = 𝟙 _)

/- Example 59.32.7 (4): for a strictly henselian local ring, positive-degree
cohomology on the small étale site of its spectrum vanishes. -/
@[stacks 03QI] #check (AlgebraicGeometry.Scheme.Etale.strictHenselianPositiveCohomologyIsZero :
    ∀ {R : Type u} [CommRing R] [StrictHenselianLocalRing R]
      [HasSheafify (Scheme.smallEtaleTopology (Spec (.of R))) AddCommGrpCat.{v}]
      [HasExt.{v} (Sheaf (Scheme.smallEtaleTopology (Spec (.of R))) AddCommGrpCat.{v})]
      (F : Sheaf (Scheme.smallEtaleTopology (Spec (.of R))) AddCommGrpCat.{v}),
      ∀ p : ℕ, 0 < p →
        IsZero ((Sheaf.functorH (Scheme.smallEtaleTopology (Spec (.of R))) p).obj F))

