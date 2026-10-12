/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PseudoCoherent.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Pullback of pseudo-coherent derived modules on ringed spaces

This leaf specializes the bundled ringed-site theorem to the canonical site of opens.  Its public
surface contains no cover, localization, or derived-category implementation parameters.
-/

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent

variable {X Y : RingedSpace.{u}}

/-- Lemma 20.47.3: derived pullback preserves `m`-pseudo-coherence. -/
@[stacks 09U7]
theorem pullback (f : X ⟶ Y)
    {E : ModuleDerived Y} {m : ℤ} (hE : IsMPseudoCoherent E m) :
    IsMPseudoCoherent ((RingedSpace.modulePullbackDerived f).obj E) m := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent
