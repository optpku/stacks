/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Depth.IdealExt
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 47.11.1 (1): the `I`-depth of `M` is the least degree in which
`CategoryTheory.Abelian.Ext (ModuleCat.of A (A ⧸ I)) (ModuleCat.of A M) i`
is nontrivial. -/
@[stacks 0AVZ] #check
  (Ideal.depthIsLeastExt :
    ∀ {A M : Type u} [CommRing A] [IsNoetherianRing A]
      [AddCommGroup M] [Module A M] [Module.Finite A M]
      (I : Ideal A),
      I • (⊤ : Submodule A M) ≠ ⊤ →
      ∃ d : ℕ, I.depth M = (d : ℕ∞) ∧
        IsLeast
          {i : ℕ | Nontrivial
            (CategoryTheory.Abelian.Ext (ModuleCat.of A (A ⧸ I))
              (ModuleCat.of A M) i)}
          d)

/- Lemma 47.11.1 (2): the `I`-depth of `M` is the least degree in which
`(localCohomology I i).obj (ModuleCat.of A M)` is not a zero object. -/
@[stacks 0AVZ] #check
  (Ideal.depthIsLeastLocalCohomology :
    ∀ {A M : Type u} [CommRing A] [IsNoetherianRing A]
      [AddCommGroup M] [Module A M] [Module.Finite A M]
      (I : Ideal A),
      I • (⊤ : Submodule A M) ≠ ⊤ →
      ∃ d : ℕ, I.depth M = (d : ℕ∞) ∧
        IsLeast
          {i : ℕ | ¬ CategoryTheory.Limits.IsZero
            ((localCohomology I i).obj (ModuleCat.of A M))}
          d)

/- Lemma 47.11.1 (3): below the `I`-depth of `M`,
`CategoryTheory.Abelian.Ext (ModuleCat.of A N) (ModuleCat.of A M) i` is
subsingleton for every finite `N` annihilated by a power of `I`. -/
@[stacks 0AVZ] #check
  (Ideal.extSubsingletonOfLtDepth :
    ∀ {A M : Type u} [CommRing A] [IsNoetherianRing A]
      [AddCommGroup M] [Module A M] [Module.Finite A M]
      (I : Ideal A),
      I • (⊤ : Submodule A M) ≠ ⊤ →
      ∀ {N : Type u} [AddCommGroup N] [Module A N] [Module.Finite A N],
        Module.IsAnnihilatedByPower I N → ∀ {i : ℕ},
          (i : ℕ∞) < I.depth M →
          Subsingleton
            (CategoryTheory.Abelian.Ext (ModuleCat.of A N)
              (ModuleCat.of A M) i))
