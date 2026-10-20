module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Comparison
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Pseudo-coherence under derived pushforward on schemes

This module records preservation and reflection of pseudo-coherence bounds by derived pushforward
along finite morphisms whose pushed-forward structure module is pseudo-coherent.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- Derived pushforward along a finite morphism preserves and reflects `m`-pseudo-coherence when
the pushed-forward structure module is pseudo-coherent. -/
@[stacks 09VB]
theorem isMPseudoCoherent_iff_pushforward_of_isFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (h_pushforwardStructure : SheafOfModules.IsPseudoCoherent
      ((Scheme.Modules.pushforward f).obj
        (SheafOfModules.unit X.ringCatSheaf : X.Modules)))
    (E : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) (m : ℤ) :
    RingedSpace.ModuleDerived.IsMPseudoCoherent E.obj m ↔
      RingedSpace.ModuleDerived.IsMPseudoCoherent
        ((pushforwardCohomologyIn f).obj E).obj m := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
