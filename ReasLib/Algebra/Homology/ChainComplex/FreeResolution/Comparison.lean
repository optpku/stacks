/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import ReasLib.Algebra.Homology.ChainComplex.FreeResolution
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison with free chain complexes

@stack 00LS

The source complex in these comparison statements is only required to be termwise free; it need
not itself resolve its augmentation target.
-/

@[expose] public section

open CategoryTheory
open ChainComplex

universe u v

namespace ChainComplex.IsTermwiseFree

variable {R : Type u} [Ring R]
variable {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable {F G : ChainComplex (ModuleCat R) ℕ}

/-- Lemma 10.71.4 (1): a map from an augmented termwise-free complex to a module lifts through
any resolution of the target module. -/
@[stacks 00LS "(1), lift to a resolution"]
theorem exists_lift_to_resolution
    (hF : ChainComplex.IsTermwiseFree F)
    (f : ModuleCat.of R M ⟶ ModuleCat.of R N)
    (πF : F ⟶ (ChainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R M))
    (πG : G ⟶ (ChainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R N))
    [QuasiIso πG] :
    ∃ α : F ⟶ G, α ≫ πG = πF ≫ (ChainComplex.single₀ (ModuleCat R)).map f := sorry

/-- Lemma 10.71.4 (2): any two augmentation-compatible lifts from a termwise-free complex to a
resolution are homotopic. -/
@[stacks 00LS "(2), uniqueness up to homotopy"]
theorem homotopic_lifts_to_resolution
    (hF : ChainComplex.IsTermwiseFree F)
    (f : ModuleCat.of R M ⟶ ModuleCat.of R N)
    (πF : F ⟶ (ChainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R M))
    (πG : G ⟶ (ChainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R N))
    [QuasiIso πG] {α β : F ⟶ G}
    (hα : α ≫ πG = πF ≫ (ChainComplex.single₀ (ModuleCat R)).map f)
    (hβ : β ≫ πG = πF ≫ (ChainComplex.single₀ (ModuleCat R)).map f) :
    homotopic (ModuleCat R) (ComplexShape.down ℕ) α β := sorry

end ChainComplex.IsTermwiseFree
