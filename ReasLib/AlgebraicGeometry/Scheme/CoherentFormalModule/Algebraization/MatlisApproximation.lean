module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.ModuleSystem
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Inequalities
public import ReasLib.Algebra.Module.Injective.Hull
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension
public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- Under the local algebraization, dualizing, cohomological-dimension, and
`(s, s + d)`-inequality hypotheses, ordinary local cohomology in degree `i ≤ s`
admits an eventual approximation by the Matlis dual of a finite module
annihilated by a power of `S.I`. The approximation has finite-length cokernels,
and the transition images of its stagewise kernel system are eventually of
finite length. -/
theorem existsMatlisDualApproximation
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (S : AffineAlgebraizationSetup A)
    (M : AffineAlgebraizationSetup.ModuleSystem S)
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
    (d s : ℤ)
    (h_cd : Ideal.LocalCohomology.HasDimensionLE S.I d)
    (hs : 0 ≤ s)
    (h_a : S.a = IsLocalRing.maximalIdeal A)
    (h_ineq : SatisfiesInequalities S (M.toFormalModule S) s (s + d))
    {E : Type u} [AddCommGroup E] [Module A E] [Module.Injective A E]
    (ι : IsLocalRing.ResidueField A →ₗ[A] E) (hι : ι.IsInjectiveHull)
    (i : ℕ) (hi : (i : ℤ) ≤ s) :
    ∃ (N : ModuleCat.{u} A),
      Module.Finite A N ∧ Module.IsAnnihilatedByPower S.I N ∧
        ∃ (n₀ : ℕ),
        ∃ (α :
          CategoryTheory.SequentialInverseSystem.shift
            (M.system ⋙ (ModuleCat.isFG A).ι ⋙
              localCohomology (IsLocalRing.maximalIdeal A) i) n₀ ⟶
            (Functor.const ℕᵒᵖ).obj (ModuleCat.of A (N →ₗ[A] E))),
          (∀ n : ℕ, IsFiniteLength A (cokernel (α.app (op n)) : ModuleCat.{u} A)) ∧
          ∃ (K : SequentialInverseSystem (ModuleCat.{u} A)),
            ∃ (κ : K ⟶
              CategoryTheory.SequentialInverseSystem.shift
                (M.system ⋙ (ModuleCat.isFG A).ι ⋙
                  localCohomology (IsLocalRing.maximalIdeal A) i) n₀),
              ∃ (hzero : ∀ n : ℕ, κ.app (op n) ≫ α.app (op n) = 0),
                ∃ (hkernel : ∀ n : ℕ,
                  IsLimit (KernelFork.ofι (κ.app (op n)) (hzero n))),
                  ∀ n' : ℕ,
                    ∃ (c : ℕ) (h_n'c : n' ≤ c),
                      ∀ (n'' : ℕ) (h_cn'' : c ≤ n''),
                        IsFiniteLength A (LinearMap.range
                          (ModuleCat.homEquiv (K.transitionMap (Nat.le_trans h_n'c h_cn'')))) := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
