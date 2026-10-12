/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.FinitePresentation

/-!
# Pullback of relative pseudo-coherence

Pullback along a pseudo-coherent scheme morphism preserves relative pseudo-coherence of
derived modules.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver

/-- Derived pullback along a pseudo-coherent morphism preserves relative
`m`-pseudo-coherence over a locally finite type base morphism. -/
theorem pullback_of_pseudoCoherent {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [PseudoCoherent f] [LocallyOfFiniteType g]
    {E : RingedSpace.ModuleDerived Y.toRingedSpace} {m : ℤ}
    (hE : IsMPseudoCoherentOver g E m) :
    IsMPseudoCoherentOver (f ≫ g)
      ((RingedSpace.modulePullbackDerived f.toShHom).obj E) m := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver
