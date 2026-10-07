module

public import ReasLib.Algebra.Homology.CochainComplex.MappingCone.SplitMonoFactorization
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Mapping-cone comparisons for degreewise-split triangles

Mathlib owns the concrete cone/rotation comparison.  This leaf supplies the fixed-endpoint
existence bridges used when a short complex is presented with a chosen degreewise splitting, and
the split-monomorphic factorization specialization.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open ComplexShape HomologicalComplex

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [HasZeroObject 𝒜]
  [HasBinaryBiproducts 𝒜]

namespace DegreewiseSplit.MappingCone

/-- A degreewise-split short complex gives a fixed-first-two-vertices comparison between its
mapping-cone triangle and its associated homotopy-category triangle. -/
@[stacks 014L "mapping-cone comparison for a degreewise-split short complex"]
theorem triangleIso
    (S : ShortComplex (CochainComplex 𝒜 ℤ))
    (σ : ∀ n : ℤ, (S.map (eval 𝒜 (up ℤ) n)).Splitting) :
    ∃ e : mappingCone.triangleh S.f ≅ trianglehOfDegreewiseSplit S σ,
      e.hom.hom₁ = 𝟙 ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj S.X₁) ∧
        e.hom.hom₂ = 𝟙 ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj S.X₂) := sorry

namespace SplitMono

/-- The canonical split-monomorphic factorization has a degreewise-split triangle comparison with
the standard mapping-cone triangle of the original map. -/
@[stacks 014L "split-monomorphic mapping-cone triangle comparison"]
theorem triangleIso
    {K L : CochainComplex 𝒜 ℤ} (f : K ⟶ L) :
    ∃ e :
        trianglehOfDegreewiseSplit
            (SplitMonoFactorization.shortComplex f)
            (SplitMonoFactorization.splitting f) ≅
          mappingCone.triangleh f,
      e.hom.hom₁ = 𝟙 ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K) := sorry

end SplitMono

end DegreewiseSplit.MappingCone

end CochainComplex
