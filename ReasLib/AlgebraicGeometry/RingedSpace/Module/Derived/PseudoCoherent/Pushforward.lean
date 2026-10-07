module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Pseudo-coherence under derived pushforward on ringed spaces

This leaf records preservation and reflection of pseudo-coherence bounds by derived pushforward
along a closed embedding whose pushed-forward structure module is pseudo-coherent.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent

/-- Derived pushforward along a closed embedding preserves and reflects `m`-pseudo-coherence when
the pushed-forward structure module is pseudo-coherent. -/
@[stacks 09VA]
theorem iff_derivedPushforward_of_isClosedEmbedding
    {X Z : RingedSpace.{u}} (i : Z ⟶ X)
    (hi : Topology.IsClosedEmbedding i.hom.base)
    (h_pushforwardStructure : SheafOfModules.IsPseudoCoherent
      ((RingedSpace.Hom.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf : Z.Modules)))
    (E : ModuleDerived Z) (m : ℤ) :
    IsMPseudoCoherent E m ↔
      IsMPseudoCoherent ((RingedSpace.moduleDerivedPushforward i).obj E) m := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent
