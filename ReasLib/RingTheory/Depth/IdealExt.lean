/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.Algebra.Homology.LocalCohomology
public import ReasLib.Algebra.Module.IdealPower.Predicate
public import ReasLib.RingTheory.Depth

@[expose] public section

open scoped ENat

universe u

namespace Ideal

variable {A M : Type u} [CommRing A] [IsNoetherianRing A]
  [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- The `I`-depth of a finite module is the least degree with nontrivial Ext from `A ⧸ I`. -/
theorem depthIsLeastExt (I : Ideal A)
    (hIM : I • (⊤ : Submodule A M) ≠ ⊤) :
    ∃ d : ℕ, I.depth M = (d : ℕ∞) ∧
      IsLeast
        {i : ℕ | Nontrivial
          (CategoryTheory.Abelian.Ext (ModuleCat.of A (A ⧸ I))
            (ModuleCat.of A M) i)}
        d := sorry

/-- The `I`-depth of a finite module is the least degree with nonzero `I`-local cohomology. -/
theorem depthIsLeastLocalCohomology (I : Ideal A)
    (hIM : I • (⊤ : Submodule A M) ≠ ⊤) :
    ∃ d : ℕ, I.depth M = (d : ℕ∞) ∧
      IsLeast
        {i : ℕ | ¬ CategoryTheory.Limits.IsZero
          ((localCohomology I i).obj (ModuleCat.of A M))}
        d := sorry

/-- If a finite module is annihilated by a power of `I`, its Ext into `M` is subsingleton below the `I`-depth of `M`. -/
theorem extSubsingletonOfLtDepth (I : Ideal A)
    (hIM : I • (⊤ : Submodule A M) ≠ ⊤)
    {N : Type u} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hN : Module.IsAnnihilatedByPower I N) {i : ℕ}
    (hi : (i : ℕ∞) < I.depth M) :
    Subsingleton
      (CategoryTheory.Abelian.Ext (ModuleCat.of A N) (ModuleCat.of A M) i) := sorry

end Ideal
