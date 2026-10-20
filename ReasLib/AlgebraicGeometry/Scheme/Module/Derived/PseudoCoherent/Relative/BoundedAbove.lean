/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent.BoundedAbove
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.Module

/-!
# Relative pseudo-coherence from local upper bounds

This file gives a termwise criterion for relative pseudo-coherence of locally bounded-above
complexes of modules on schemes.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver

/-- A locally bounded-above complex whose term in degree `i` is relatively
`(m - i)`-pseudo-coherent has relatively `m`-pseudo-coherent derived realization. -/
theorem of_locallyBoundedAbove_of_termwise {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (K : CochainComplex X.Modules ℤ) (m : ℤ)
    (hK : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hterm : ∀ i : ℤ, (K.X i).IsMPseudoCoherentOver f (m - i)) :
    IsMPseudoCoherentOver f (DerivedCategory.Q.obj K) m := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver
