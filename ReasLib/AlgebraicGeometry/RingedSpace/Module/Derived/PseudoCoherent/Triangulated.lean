module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PseudoCoherent.Triangulated
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Triangles of pseudo-coherent derived modules on ringed spaces

This is the ringed-space facade for the bundled ringed-site closure API.  Its statements expose
only the triangle and the degree bounds used by downstream geometry.
-/

open CategoryTheory CategoryTheory.Pretriangulated

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent

variable {X : RingedSpace.{u}}

/-- Shifting by `n` translates the pseudo-coherence bound by `n`. -/
theorem shift_iff (K : ModuleDerived X) (n m : ℤ) :
    IsMPseudoCoherent (K⟦n⟧) (m - n) ↔ IsMPseudoCoherent K m := sorry

/-- Lemma 20.47.4 (1): the third vertex inherits the indicated pseudo-coherence bound. -/
@[stacks 08CD "(1)"]
theorem obj₃ {m : ℤ} (T : Triangle (ModuleDerived X))
    (hT : T ∈ distTriang (ModuleDerived X))
    (h₁ : IsMPseudoCoherent T.obj₁ (m + 1))
    (h₂ : IsMPseudoCoherent T.obj₂ m) :
    IsMPseudoCoherent T.obj₃ m := sorry

/-- Lemma 20.47.4 (2): the middle vertex inherits the common pseudo-coherence bound. -/
@[stacks 08CD "(2)"]
theorem obj₂ {m : ℤ} (T : Triangle (ModuleDerived X))
    (hT : T ∈ distTriang (ModuleDerived X))
    (h₁ : IsMPseudoCoherent T.obj₁ m)
    (h₃ : IsMPseudoCoherent T.obj₃ m) :
    IsMPseudoCoherent T.obj₂ m := sorry

/-- Lemma 20.47.4 (3): the first vertex inherits the shifted pseudo-coherence bound. -/
@[stacks 08CD "(3)"]
theorem obj₁ {m : ℤ} (T : Triangle (ModuleDerived X))
    (hT : T ∈ distTriang (ModuleDerived X))
    (h₂ : IsMPseudoCoherent T.obj₂ (m + 1))
    (h₃ : IsMPseudoCoherent T.obj₃ m) :
    IsMPseudoCoherent T.obj₁ (m + 1) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent
