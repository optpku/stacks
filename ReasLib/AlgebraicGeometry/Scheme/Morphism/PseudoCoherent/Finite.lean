module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.ChangeOfBase
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent

/-!
# Pseudo-coherent finite morphisms of schemes

This module relates pseudo-coherence of a finite scheme morphism to pseudo-coherence of the
pushforward of its structure sheaf.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.PseudoCoherent

/-- A finite morphism of schemes is pseudo-coherent if and only if the pushforward of its
structure sheaf is pseudo-coherent as a module. -/
theorem iff_pushforward_of_isFinite {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] :
    PseudoCoherent f ↔
      SheafOfModules.IsPseudoCoherent
        ((Scheme.Modules.pushforward f).obj
          (SheafOfModules.unit X.ringCatSheaf : X.Modules)) := sorry

end AlgebraicGeometry.PseudoCoherent
