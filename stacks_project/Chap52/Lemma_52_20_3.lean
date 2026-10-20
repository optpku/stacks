module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.MatlisApproximation
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

/- Lemma 52.20.3: the local-cohomology system admits an eventual compatible
   approximation by a Matlis dual with finite-length cokernels and kernel
   transition images. Ordinary module cohomology uses the nonnegative-degree
   convention `i : ℕ`, with `(i : ℤ) ≤ s`. -/
@[stacks 0EHK] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.existsMatlisDualApproximation :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (S : AlgebraicGeometry.AffineAlgebraizationSetup A)
      (M : AlgebraicGeometry.AffineAlgebraizationSetup.ModuleSystem S)
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (h_dualizing :
        ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
      (d s : ℤ)
      (h_cd : Ideal.LocalCohomology.HasDimensionLE S.I d)
      (hs : 0 ≤ s)
      (h_a : S.a = IsLocalRing.maximalIdeal A)
      (h_ineq :
        AlgebraicGeometry.Scheme.CoherentFormalModules.SatisfiesInequalities
          S (M.toFormalModule S) s (s + d))
      {E : Type u} [AddCommGroup E] [Module A E] [Module.Injective A E]
      (ι : IsLocalRing.ResidueField A →ₗ[A] E) (hι : ι.IsInjectiveHull)
      (i : ℕ) (hi : (i : ℤ) ≤ s),
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
                            (ModuleCat.homEquiv (K.transitionMap (Nat.le_trans h_n'c h_cn'')))))
