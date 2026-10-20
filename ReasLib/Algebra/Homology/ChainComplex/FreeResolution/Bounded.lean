module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.FiniteFreeResolution
public import ReasLib.Algebra.Homology.ChainComplex.Bounded
public import ReasLib.Algebra.Homology.ChainComplex.FreeResolution

/-!
# Bounded free resolutions

This leaf owns bounded free- and finite-free-resolution predicates for modules.  The underlying
support condition is `ChainComplex.IsBoundedLE`, so it remains available independently of
augmentations, resolutions, and module structure.  Local-ring and Noetherian hypotheses belong
to existence and comparison results in downstream commutative-algebra leaves.  The finite-free
chain-complex predicate is deliberately separate from the recursive module-level
`Module.HasLengthFiniteFreeResolution`; the latter is a finite-syzygy condition, not a bounded
augmented-complex witness.
@stack 064P
-/

@[expose] public section

open CategoryTheory

universe u v

namespace ChainComplex

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {F : ChainComplex (ModuleCat R) ℕ}

namespace FreeResolution

/-- A module admits a free resolution of length at most `d`. -/
@[stacks 0CXD "free resolution of bounded length"]
def HasLengthLE
    (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] (d : ℕ) : Prop :=
  ∃ (F : ChainComplex (ModuleCat R) ℕ) (π : F ⟶ moduleSingle R M),
    IsFreeResolution π ∧ ChainComplex.IsBoundedLE F d

/-- Increasing a free-resolution length bound preserves the existence of a bounded free
resolution. -/
@[stacks 0CXD "monotonicity of bounded free resolutions"]
theorem HasLengthLE.of_le
    {d e : ℕ} (hM : HasLengthLE R M d) (hde : d ≤ e) :
    HasLengthLE R M e := sorry

/-- A free resolution has length at most zero precisely when its target module is free. -/
@[stacks 0CXD "zero-length free resolution"]
theorem HasLengthLE.zero_iff
    (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] :
    HasLengthLE R M 0 ↔ Module.Free R M := sorry

/-- A free presentation together with a bounded free resolution of its kernel extends to a bounded
free resolution of the target. -/
@[stacks 0CXD "successor step for bounded free resolutions"]
theorem HasLengthLE.succ_of_freePresentation
    {d : ℕ} {P₀ : ModuleCat R} (π₀ : P₀ ⟶ ModuleCat.of R M)
    (hπ₀ : Function.Surjective π₀.hom) (hP₀ : Module.Free R P₀)
    (hK : HasLengthLE R (LinearMap.ker π₀.hom) d) :
    HasLengthLE R M (d + 1) := sorry

/-- The positive-degree tail of a bounded free resolution is a bounded free resolution of the
kernel of its augmentation. -/
@[stacks 0CXD "tail of a bounded free resolution"]
theorem HasLengthLE.tail
    {d : ℕ} (π : F ⟶ moduleSingle R M) (hπ : IsFreeResolution π)
    (hF : ChainComplex.IsBoundedLE F (d + 1)) :
    HasLengthLE R (LinearMap.ker (π.f 0).hom) d := sorry

/-- A positive-length free resolution begins with a surjective free presentation whose kernel
has the remaining shorter free resolution. -/
@[stacks 0CXD "free presentation from a bounded free resolution"]
theorem HasLengthLE.exists_freePresentation
    {n : ℕ} (hM : HasLengthLE R M (n + 1)) :
    ∃ (P₀ : ModuleCat R) (π₀ : P₀ ⟶ ModuleCat.of R M),
      Function.Surjective π₀.hom ∧
        Module.Free R P₀ ∧
          HasLengthLE R (LinearMap.ker π₀.hom) n := sorry

/-- The positive-length free-resolution predicate is exactly its free-presentation recurrence. -/
@[stacks 0CXD "bounded free resolution successor recurrence"]
theorem HasLengthLE.succ_iff
    (n : ℕ) :
    HasLengthLE R M (n + 1) ↔
      ∃ (P₀ : ModuleCat R) (π₀ : P₀ ⟶ ModuleCat.of R M),
        Function.Surjective π₀.hom ∧
          Module.Free R P₀ ∧
            HasLengthLE R (LinearMap.ker π₀.hom) n := sorry

end FreeResolution

namespace FiniteFreeResolution

/-- A module admits a bounded augmented chain-complex resolution by finite free modules of length
at most `d`.

This is the chain-complex/projective-dimension owner.  It is intentionally distinct from
`Module.HasLengthFiniteFreeResolution`: that recursive module predicate has a finite (rather than
finite-free) zero branch and records finite syzygies without a bounded chain-complex witness. -/
@[stacks 0CXD "finite free resolution of bounded length"]
def HasLengthLE
    (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] (d : ℕ) : Prop :=
  ∃ (F : ChainComplex (ModuleCat R) ℕ) (π : F ⟶ moduleSingle R M),
    IsFiniteFreeResolution π ∧ ChainComplex.IsBoundedLE F d

/-- Increasing a finite-free-resolution length bound preserves the existence of a bounded finite
free resolution. -/
@[stacks 0CXD "monotonicity of bounded finite free resolutions"]
theorem HasLengthLE.of_le
    {d e : ℕ} (hM : HasLengthLE R M d) (hde : d ≤ e) :
    HasLengthLE R M e := sorry

/-- A finite free resolution has length at most zero precisely when its target module is finite
free. -/
@[stacks 0CXD "zero-length finite free resolution"]
theorem HasLengthLE.zero_iff
    (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] :
    HasLengthLE R M 0 ↔ Module.Free R M ∧ Module.Finite R M := sorry

/-- Forgetting termwise finiteness turns a bounded finite free resolution into a bounded free
resolution of the same length. -/
@[stacks 0CXD "finite free resolution forgetful map"]
theorem HasLengthLE.forget
    {d : ℕ} (hM : HasLengthLE R M d) :
    FreeResolution.HasLengthLE R M d := sorry

/-- A module with a bounded finite free resolution is finite. -/
@[stacks 0CXD "finiteness from a bounded finite free resolution"]
theorem HasLengthLE.finite
    {d : ℕ} (hM : HasLengthLE R M d) :
    Module.Finite R M := sorry

/-- A bounded finite-free chain resolution implies the recursive module-level finite-free
resolution predicate at the same bound.

The two predicates intentionally have different owners: `HasLengthLE` records an actual bounded
augmented chain complex and hence a projective-dimension-style condition, whereas
`Module.HasLengthFiniteFreeResolution` records the weaker finite-syzygy condition.  This
forgetful direction is canonical; the converse is not asserted here. -/
@[stacks 064P "bounded finite-free resolution to module length"]
theorem HasLengthLE.toModuleLength
    {d : ℕ} (hM : HasLengthLE R M d) :
    Module.HasLengthFiniteFreeResolution R M d := sorry

/-- The positive-degree tail of a bounded finite free resolution is a bounded finite free
resolution of the kernel of its augmentation. -/
@[stacks 0CXD "tail of a bounded finite free resolution"]
theorem HasLengthLE.tail
    {d : ℕ} (π : F ⟶ moduleSingle R M) (hπ : IsFiniteFreeResolution π)
    (hF : ChainComplex.IsBoundedLE F (d + 1)) :
    HasLengthLE R (LinearMap.ker (π.f 0).hom) d := sorry

/-- A finite free presentation together with a bounded finite free resolution of its kernel
extends to a bounded finite free resolution of the target. -/
@[stacks 0CXD "successor step for bounded finite free resolutions"]
theorem HasLengthLE.succ_of_finiteFreePresentation
    {d : ℕ} {P₀ : ModuleCat R} (π₀ : P₀ ⟶ ModuleCat.of R M)
    (hπ₀ : Function.Surjective π₀.hom) (hP₀ : Module.Free R P₀)
    (hP₀finite : Module.Finite R P₀)
    (hK : HasLengthLE R (LinearMap.ker π₀.hom) d) :
    HasLengthLE R M (d + 1) := sorry

/-- A positive-length finite free resolution begins with a surjective finite free presentation
whose kernel has the remaining shorter finite free resolution. -/
@[stacks 0CXD "finite free presentation from a bounded finite free resolution"]
theorem HasLengthLE.exists_finiteFreePresentation
    {n : ℕ} (hM : HasLengthLE R M (n + 1)) :
    ∃ (P₀ : ModuleCat R) (π₀ : P₀ ⟶ ModuleCat.of R M),
      Function.Surjective π₀.hom ∧
        Module.Free R P₀ ∧
          Module.Finite R P₀ ∧
            HasLengthLE R (LinearMap.ker π₀.hom) n := sorry

/-- The positive-length finite-free-resolution predicate is exactly its finite-free-presentation
recurrence. -/
@[stacks 0CXD "bounded finite free resolution successor recurrence"]
theorem HasLengthLE.succ_iff
    (n : ℕ) :
    HasLengthLE R M (n + 1) ↔
      ∃ (P₀ : ModuleCat R) (π₀ : P₀ ⟶ ModuleCat.of R M),
        Function.Surjective π₀.hom ∧
          Module.Free R P₀ ∧
            Module.Finite R P₀ ∧
              HasLengthLE R (LinearMap.ker π₀.hom) n := sorry

end FiniteFreeResolution

end ChainComplex
