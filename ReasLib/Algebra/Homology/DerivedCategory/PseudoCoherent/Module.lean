/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.ChainComplex.FreeResolution
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Cohomology
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Triangulated
public import ReasLib.Algebra.Module.FiniteFreeResolution
public import ReasLib.Algebra.Module.FinitePresentation.Exact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pseudo-coherent modules

For modules concentrated in degree zero, pseudo-coherence records the length of a finite-free
resolution.  The first two bounds recover finite generation and finite presentation, while all
bounds together recover an infinite termwise finite-free resolution.

@stack 064T
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.ModuleCat.IsMPseudoCoherent

variable {R : Type u} [Ring R]

/-- A finite free module is `m`-pseudo-coherent for every integer `m`. -/
theorem of_finiteFree (M : ModuleCat R) (m : ℤ)
    [Module.Free R M] [Module.Finite R M] :
    M.IsMPseudoCoherent m := sorry

/-- Lemma 15.65.4 (1): a module is `0`-pseudo-coherent exactly when it is finite. -/
@[stacks 064T "(1)"]
theorem zero_iff_finite (M : ModuleCat R) :
    M.IsMPseudoCoherent 0 ↔ Module.Finite R M := sorry

/-- Lemma 15.65.4 (2): a module is `(-1)`-pseudo-coherent exactly when it is finitely
presented. -/
@[stacks 064T "(2)"]
theorem minusOne_iff_finitePresentation (M : ModuleCat R) :
    M.IsMPseudoCoherent (-1) ↔ Module.FinitePresentation R M := sorry

/-- Lemma 15.65.4 (3): `(-d)`-pseudo-coherence is equivalent to admitting a length-`d`
finite-free resolution. -/
@[stacks 064T "(3)"]
theorem neg_iff_hasLengthFiniteFreeResolution (M : ModuleCat R) (d : ℕ) :
    M.IsMPseudoCoherent (-(d : ℤ)) ↔
      Module.HasLengthFiniteFreeResolution R M d := sorry

end CategoryTheory.ModuleCat.IsMPseudoCoherent

namespace CategoryTheory.ModuleCat.IsPseudoCoherent

variable {R : Type u} [Ring R]

/-- A finite-free resolution supplies a pseudo-coherent derived module. -/
theorem of_finiteFreeResolution
    {M : ModuleCat R} {F : ChainComplex (ModuleCat R) ℕ}
    (π : F ⟶ ChainComplex.moduleSingle R M)
    [ChainComplex.IsFiniteFreeResolution π] :
    M.IsPseudoCoherent := sorry

/-- Lemma 15.65.4 (4): a module is pseudo-coherent exactly when it admits a resolution by
finite free modules. -/
@[stacks 064T "(4)"]
theorem iff_exists_finiteFreeResolution (M : ModuleCat R) :
    M.IsPseudoCoherent ↔
      ∃ (F : ChainComplex (ModuleCat R) ℕ) (π : F ⟶ ChainComplex.moduleSingle R M),
        ChainComplex.IsFiniteFreeResolution π := sorry

end CategoryTheory.ModuleCat.IsPseudoCoherent
