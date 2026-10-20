module

public import Mathlib.Data.List.TFAE
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.GlobalDimension.IdealQuotient

/-!
# Testing global dimension on finite modules

For a commutative ring, a uniform projective-dimension bound may be tested on all finite modules
or, more economically, on all ideal quotients. The binary characterizations are the primary API;
the three-way statement records the source-facing presentation.
-/

@[expose] public section

open CategoryTheory

universe u

namespace HasGlobalDimensionLE

variable {R : Type u} [CommRing R]

/-- A global-dimension bound on a commutative ring is equivalent to the same bound on every
finite module. -/
@[stacks 065T "finite-module characterization"]
theorem iff_finiteModules (n : ℕ) :
    HasGlobalDimensionLE R n ↔
      ∀ (M : ModuleCat.{u} R) [Module.Finite R M], HasProjectiveDimensionLE M n := sorry

/-- Lemma 10.109.12 (Stacks `065T`): global dimension at most `n`, the corresponding bound on
all finite modules, and the corresponding bound on all ideal quotients are equivalent. -/
@[stacks 065T]
theorem tfae_finite_idealQuotients (n : ℕ) :
    List.TFAE
      [ HasGlobalDimensionLE R n,
        ∀ (M : ModuleCat.{u} R) [Module.Finite R M], HasProjectiveDimensionLE M n,
        ∀ I : Ideal R, HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ I)) n ] := sorry

end HasGlobalDimensionLE
